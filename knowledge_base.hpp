#ifndef KNOWLEDGE_BASE_HPP
#define KNOWLEDGE_BASE_HPP
#include <list>
#include "definite_clause.hpp"
#include "substitution.hpp"
#include "../cpp_common/combinator.hpp"
namespace first_order_logic
{
    struct knowledge_base
    {
        std::vector< definite_clause > kb;
        std::vector< atomic_sentence > known_facts;
        template< typename ITER >
        ITER matching_facts( const atomic_sentence & match, const substitution & sub, ITER result ) const
        {
            for ( auto i = known_facts.begin( ); i != known_facts.end( ); ++i )
            {
                const auto & sen = * i;
                assert( static_cast< bool >( sen.data ) );
                auto res = unify( match, sen, sub );
                if ( res ) { * result = std::make_pair( sen, * res ); }
            }
            return result;
        }
        std::set< std::string > variable_name( )
        {
            std::set< std::string > ret;
            auto extract =
                    [&]( const atomic_sentence & s )
            { cv( s, make_function_output_iterator( [&]( const term & t ){ ret.insert( t->name ); } ) ); };
            for ( const definite_clause & dc : kb )
            {
                std::for_each( dc.premise.begin( ), dc.premise.end( ), extract );
                extract( dc.conclusion );
            }
            return ret;
        }
        bool try_infer_forward(
                const std::vector< atomic_sentence > & premise,
                const atomic_sentence & conclusion,
                const substitution & rename,
                const atomic_sentence & query )
        {
            bool ret = false;
            std::vector< atomic_sentence > new_known_facts;
            substitution s;
            std::vector< atomic_sentence > gp;
            common::fix(
                [&,this]( const auto & self, const substitution & sub )->void
                {
                    if ( gp.size( ) == premise.size( ) )
                    { new_known_facts.push_back( sub( rename( conclusion ) ) ); }
                    else
                    {
                        this->matching_facts(
                                rename( premise[ gp.size( ) ] ),
                                sub,
                                make_function_output_iterator(
                                    [&]( const auto & p )
                                    {
                                        if ( ( new_known_facts.empty( ) ) ||
                                             ( ! unify( new_known_facts.back( ), query ) ) )
                                        {
                                            gp.push_back( p.first );
                                            self( p.second );
                                            gp.pop_back( );
                                        }
                                    } ) );
                    }
                } )( s );
            for ( const atomic_sentence & sen : new_known_facts )
            {
                if ( std::none_of(
                        known_facts.begin( ),
                        known_facts.end( ),
                        [&]( const atomic_sentence & s )
                        { return unify( sen, s ); } ) )
                {
                    known_facts.push_back( sen );
                    ret = true;
                }
            }
            return ret;
        }
        boost::optional< substitution > forward_chaining( const atomic_sentence & sen )
        {
            for ( const atomic_sentence & se : known_facts )
            {
                auto ret = unify( se, sen );
                if ( ret ) { return ret; }
            }
            bool have_new_inference = true;
            std::set< std::string > var_name = variable_name( );
            while ( have_new_inference )
            {
                have_new_inference = false;
                for ( const definite_clause & dc : kb )
                {
                    assert( ! dc.premise.empty( ) );
                    substitution rename =
                            rename_variable(
                                dc.premise.begin( ),
                                dc.premise.end( ),
                                [&]( const std::string & v )
                    { return var_name.count( v ) == 0; },
                    []( const std::string & n ) { return n + "_"; } );
                    have_new_inference =
                            try_infer_forward( dc.premise, dc.conclusion, rename, sen ) ||
                            have_new_inference;
                    auto ret = unify( known_facts.back( ), sen );
                    if ( ret ) { return ret; }
                }
            }
            return boost::optional< substitution >( );
        }
        boost::optional< substitution > backward_chaining( const atomic_sentence & sen )
        {
            for ( const atomic_sentence & se : known_facts )
            {
                auto ret = unify( se, sen );
                if ( ret ) { return ret; }
            }
            if ( known_facts.empty( ) ) { return boost::optional< substitution >( ); }
            std::set< std::string > var_name = variable_name( );
            std::map< atomic_sentence, std::vector< std::vector< atomic_sentence > > > requiring_fact;
            bool progress = true;
            auto try_add =
                    [&]( const atomic_sentence & s )
            {
                if ( requiring_fact.count( s ) == 0 )
                {
                    std::vector< std::vector< atomic_sentence > > deduct_from;
                    for ( const definite_clause & dc : kb )
                    {
                        assert( ! dc.premise.empty( ) );
                        substitution rename =
                                rename_variable(
                                    dc.premise.begin( ),
                                    dc.premise.end( ),
                                    [&]( const std::string & v ){
                            return var_name.count( v ) == 0; },
                        []( const std::string & n )
                        { return n + "_"; } );
                        auto ret = unify( rename( dc.conclusion ), s );
                        if ( ret )
                        {
                            std::vector< atomic_sentence > tem;
                            for ( const atomic_sentence & se : dc.premise )
                            { tem.push_back( ( *ret )( rename( se ) ) ); }
                            deduct_from.push_back( tem );
                        }
                    }
                    requiring_fact.insert( std::make_pair( s, deduct_from ) );
                    progress = true;
                }
            };
            try_add( sen );
            while ( progress )
            {
                progress = false;
                auto ret = unify( known_facts.back( ), sen );
                if ( ret ) { return ret; }
                std::vector< atomic_sentence > add;
                for ( const auto & p : requiring_fact )
                {
                    for ( const auto & vec : p.second )
                    {
                        substitution rename =
                                rename_variable(
                                    vec.begin( ),
                                    vec.end( ),
                                    [&]( const std::string & v )
                        { return var_name.count( v ) == 0; },
                        []( const std::string & n )
                        { return n + "_"; } );
                        progress = try_infer_forward( vec, p.first, rename, sen ) || progress;
                        auto ret = unify( known_facts.back( ), sen );
                        if ( ret ) { return ret; }
                        std::copy( vec.begin( ), vec.end( ), std::back_inserter( add ) );
                    }
                }
                std::for_each( add.begin( ), add.end( ), try_add );
            }
            return boost::optional< substitution >( );
        }
    };
}
#endif // KNOWLEDGE_BASE_HPP
