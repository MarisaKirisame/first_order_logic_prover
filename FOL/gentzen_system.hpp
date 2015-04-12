#ifndef FIRST_ORDER_LOGIC_FOL_GENTZEN_SYSTEM_HPP
#define FIRST_ORDER_LOGIC_FOL_GENTZEN_SYSTEM_HPP
#include "satisfiability.hpp"
#include "sentence/predicate.hpp"
#include "memory"
#include "utility"
#include "term_generator.hpp"
#include "boost/range.hpp"
#include "boost/range/join.hpp"
#include "boost/iterator/counting_iterator.hpp"
#include "sentence/function.hpp"
#include "proof_tree.hpp"
#include "sentence/sentence.hpp"
#include "forward/first_order_logic.hpp"
#include "sentence/substitution.hpp"
#include <experimental/optional>
#include "sentence/sentence_operations.hpp"
namespace first_order_logic
{
    struct gentzen_system
    {
        struct sequence
        {
            proof_tree pt;
            term new_variable( )
            {
                term ret = make_variable( std::to_string( unused++ ) );
                cv_map.insert( std::make_pair( ret, std::set< free_sentence >( ) ) );
                return ret;
            }
            std::map< free_sentence, bool > sequent;
            std::map< free_sentence, bool > temp_sequent;
            std::map
            <
                term,
                std::set< free_sentence >
            > cv_map, term_map;
            std::map< free_sentence, bool > expanded;
            size_t unused = 0;
            std::set< function > functions;
            std::set< predicate > predicates;
            term_generator< sequence > tg;
            std::vector< std::tuple< sequence, proof_tree, std::experimental::optional< validity > > > branch;
            sequence * parent = nullptr;
            struct contradiction { proof_tree pt; };
            void try_insert(
                std::map< free_sentence, bool > & m,
                const free_sentence & t,
                bool b )
            {
                if ( m.insert( std::make_pair( t, b ) ).first->second != b )
                {
                    contradiction con;
                    auto res = pair_str( );
                    std::string & str = b ? res.first : res.second;
                    if ( ! str.empty( ) ) { str += ","; }
                    str += static_cast< std::string >( t );
                    con.pt = ( res.first + "-->" + res.second );
                    throw con;
                }
            }
            void add_equal_generator( const function & f )
            {
                assert( f.arity >= 1 );
                if ( f.arity == 1 )
                {
                    try_insert
                    (
                        sequent,
                        make_all
                        (
                            variable( "s" ),
                            variable( "t" ),
                            make_imply
                            (
                                make_equal(
                                    make_variable( "s" ),
                                    make_variable( "t" ) ),
                                make_equal
                                (
                                    make_function(
                                        f.name,
                                        { make_variable( "s" ) } ),
                                    make_function(
                                        f.name,
                                        { make_variable( "t" ) } )
                                )
                            )
                        ),
                        true
                    );
                }
                else
                {
                    std::vector< term > args, argt;
                    args.reserve( f.arity );
                    argt.reserve( f.arity );
                    std::for_each(
                        boost::counting_iterator< size_t >( 0 ),
                        boost::counting_iterator< size_t >( f.arity ),
                        [&]( size_t i )
                        {
                            args.push_back(
                                make_variable( "s" + std::to_string( i ) ) );
                            argt.push_back(
                                make_variable( "t" + std::to_string( i ) ) );
                        } );
                    free_sentence and_stack =
                            make_and(
                                make_equal( args[0], argt[0] ),
                            make_equal( args[1], argt[1] ) );
                    for ( size_t i = 2; i < f.arity; ++i )
                    {
                        and_stack =
                                make_and( and_stack, make_equal( args[i], argt[i] ) );
                    }
                    auto add =
                            make_imply(
                                and_stack,
                                make_equal(
                                    make_function( f.name, args ),
                                    make_function( f.name, argt ) ) );
                    for ( size_t i = 0; i < f.arity; ++i )
                    {
                        add = make_all(
                                    args[i]->name,
                                    make_all( argt[i]->name, add ) );
                    }
                    try_insert( sequent, add, true );
                }
            }
            void add_equal_generator( const predicate & f )
            {
                assert( f.arity >= 1 );
                if ( f.arity == 1 )
                {
                    try_insert
                    (
                        sequent,
                        make_all
                        (
                            variable( "s" ),
                            variable( "t" ),
                            make_imply
                            (
                                make_and
                                (
                                    make_equal(
                                        make_variable( "s" ),
                                        make_variable( "t" ) ),
                                    make_predicate(
                                        f.name,
                                        { make_variable( "s" ) } )
                                ),
                                make_predicate(
                                    f.name,
                                    { make_variable( "t" ) } )
                            )
                        ),
                        true
                    );
                }
                else
                {
                    std::vector< term > args, argt;
                    args.reserve( f.arity );
                    argt.reserve( f.arity );
                    std::for_each(
                        boost::counting_iterator< size_t >( 0 ),
                        boost::counting_iterator< size_t >( f.arity ),
                        [&]( size_t i )
                        {
                            args.push_back(
                                make_variable( "s" + std::to_string( i ) ) );
                            argt.push_back(
                                make_variable( "t" + std::to_string( i ) ) );
                        } );
                    free_sentence and_stack =
                            make_and(
                                make_equal( args[0], argt[0] ),
                                make_equal( args[1], argt[1] ) );
                    try_insert(
                        sequent,
                        make_imply(
                            make_and( and_stack, make_predicate( f.name, args ) ),
                            make_predicate( f.name, argt ) ),
                        true );
                }
            }
            void add_equal_generator( )
            {
                try_insert(
                    sequent,
                    make_all(
                        variable( "t" ),
                        make_equal( make_variable( "t" ), make_variable( "t" ) ) ),
                    true );
                try_insert( sequent,
                            make_all
                            (
                                variable( "x" ),
                                variable( "y" ),
                                make_imply
                                (
                                    make_equal(
                                        make_variable( "x" ),
                                        make_variable( "y" ) ),
                                    make_equal(
                                        make_variable( "y" ),
                                        make_variable( "x" ) )
                                )
                            ), true );
                try_insert( sequent,
                            make_all
                            (
                                variable( "s1" ),
                                variable( "t1" ),
                                variable( "s2" ),
                                variable( "t2" ),
                                make_imply
                                (
                                    make_and
                                    (
                                        make_equal(
                                            make_variable( "s1" ),
                                            make_variable( "t1" ) ),
                                        make_equal(
                                            make_variable( "s2" ),
                                            make_variable( "t2" ) ),
                                        make_equal(
                                            make_variable( "s1" ),
                                            make_variable( "s2" ) )
                                    ),
                                    make_equal(
                                        make_variable( "t1" ),
                                        make_variable( "t2" ) )
                                )
                            ),
                            true );
                std::for_each(
                    functions.begin( ),
                    functions.end( ),
                    [this]( const function & f ) { add_equal_generator( f ); } );
                std::for_each(
                    predicates.begin( ),
                    predicates.end( ),
                    [this]( const predicate & f ) { add_equal_generator( f ); } );
            }
            explicit operator std::string( ) const
            {
                auto res = pair_str( );
                return res.first + "-->" + res.second;
            }
            std::pair< std::string, std::string > pair_str( ) const
            {
                std::string postive, negative;
                auto function = [&]( const std::pair< free_sentence, bool > & val )
                {
                    std::string & str = val.second ? postive : negative;
                    if ( ! str.empty( ) ) { str += ","; }
                    str += static_cast< std::string >( val.first );
                };
                std::for_each( temp_sequent.begin( ), temp_sequent.end( ), function );
                std::for_each( sequent.begin( ), sequent.end( ), function );
                std::for_each( expanded.begin( ), expanded.end( ), function );
                return std::make_pair( postive, negative );
            }
            std::experimental::optional< validity > expand( proof_tree & leaf )
            {
                if ( ! branch.empty( ) )
                {
                    auto try_join =
                        [&]( )->std::experimental::optional< validity >
                        {
                            if ( std::all_of(
                                    branch.begin( ),
                                    branch.end( ),
                                    [&]( const auto & t ) { return std::get< 2 >( t ) == validity::valid; } ) )
                            {
                                std::for_each(
                                    branch.begin( ),
                                    branch.end( ),
                                    [&]( const auto & t ) { leaf.join( std::get< 1 >( t ) ); } );
                                return validity::valid;
                            }
                            auto it =
                                std::find_if(
                                    branch.begin( ),
                                    branch.end( ),
                                    [&]( const auto & t ) { return std::get< 2 >( t ) == validity::invalid; } );
                            if ( it != branch.end( ) )
                            {
                                leaf.join( std::get< 1 >( * it ) );
                                return validity::invalid;
                            }
                            return std::experimental::optional< validity >( );
                        };
                    for ( auto & p : branch )
                    {
                        if ( ! std::get< 2 >( p ) )
                        {
                            std::get< 2 >( p ) =
                                std::get< 0 >( p ).expand( std::get< 1 >( p ) );
                            auto ret = try_join( );
                            if ( ret ) { return ret; }
                        }
                    }
                    return try_join( );
                }
                if ( sequent.empty( ) )
                {
                    sequent.swap( temp_sequent );
                    auto f = tg.generate( );
                    assert( f.size( ) == 1 );
                    term_map.insert( std::make_pair( f[0], std::set< free_sentence >( ) ) );
                }
                if ( sequent.empty( ) ) { return validity::invalid; }
                while ( ( ! sequent.empty( ) ) && branch.empty( ) )
                {
                    std::pair< free_sentence, bool > t = * sequent.begin( );
                    sequent.erase( sequent.begin( ) );
                    auto try_subsitute_term =
                            [&,this](
                                bool b,
                                const variable & var,
                                const free_sentence & sen )
                            {
                                std::for_each
                                (
                                    term_map.begin( ),
                                    term_map.end( ),
                                    [&,this]( auto & s )
                                    {
                                        if ( s.second.count( t.first ) == 0 )
                                        {
                                            s.second.insert( t.first );
                                            this->try_insert
                                            (
                                                sequent,
                                                substitution( { {
                                                    var,
                                                    s.first } }
                                                )( sen ),
                                                b
                                            );
                                        }
                                    }
                                );
                                try_insert( temp_sequent, t.first, b );
                            };
                    auto try_subsitute_skolem =
                            [&,this](
                                bool b,
                                const variable & var,
                                const free_sentence & sen )
                            {
                                try_insert(
                                    sequent,
                                    substitution
                                    (
                                        {
                                            {
                                                var,
                                                term( new_variable( ) )
                                            }
                                        }
                                    )( sen ),
                                    b );
                            };
                    try
                    {
                        t.first.type_restore_full< void >
                        (
                            make_all_actor(
                                [&]( const variable & var, const free_sentence & sen )
                                {
                                    if ( t.second )
                                    { try_subsitute_term( true, var, sen ); }
                                    else
                                    { try_subsitute_skolem( false, var, sen ); }
                                } ),
                            make_some_actor(
                                [&]( const variable & var, const free_sentence & sen )
                                {
                                    if ( t.second )
                                    { try_subsitute_skolem( true, var, sen ); }
                                    else
                                    { try_subsitute_term( false, var, sen ); }
                                } ),
                            make_atomic_actor(
                                [&]( const atomic_sentence & as )
                                { try_insert( expanded, as, t.second ); } ),
                            make_and_actor(
                                [&]( const free_sentence & l, const free_sentence & r )
                                {
                                    if ( t.second )
                                    {
                                        try_insert( sequent, l, true );
                                        try_insert( sequent, r, true );
                                    }
                                    else
                                    {
                                        assert( branch.empty( ) );
                                        sequence ldt( * this );
                                        sequence rdt( * this );
                                        try
                                        {
                                            ldt.try_insert(
                                                ldt.sequent,
                                                l,
                                                false );
                                            branch.push_back(
                                                std::make_tuple
                                                (
                                                    ldt,
                                                    proof_tree( ),
                                                    std::experimental::optional< validity >( )
                                                ) );
                                        }
                                        catch ( contradiction & con )
                                        { pt.join( con.pt ); }
                                        try
                                        {
                                            rdt.try_insert(
                                                rdt.sequent,
                                                r,
                                                false );
                                            branch.push_back(
                                                std::make_tuple
                                                (
                                                    rdt,
                                                    proof_tree( ),
                                                    std::experimental::optional< validity >( )
                                                ) );
                                        }
                                        catch ( contradiction & con )
                                        { pt.join( con.pt ); }
                                    }
                                } ),
                            make_or_actor(
                                [&]( const free_sentence & l, const free_sentence & r )
                                {
                                    if ( t.second )
                                    {
                                        assert( branch.empty( ) );
                                        sequence ldt( * this );
                                        sequence rdt( * this );
                                        try
                                        {
                                            ldt.try_insert(
                                                ldt.sequent,
                                                l,
                                                true );
                                            branch.push_back(
                                                std::make_tuple
                                                (
                                                    ldt,
                                                    proof_tree( ),
                                                    std::experimental::optional< validity >( )
                                                ) );
                                        }
                                        catch ( contradiction & con )
                                        { pt.join( con.pt ); }
                                        try
                                        {
                                            rdt.try_insert(
                                                rdt.sequent,
                                                r,
                                                true );
                                            branch.push_back(
                                                std::make_tuple
                                                (
                                                    rdt,
                                                    proof_tree( ),
                                                    std::experimental::optional< validity >( )
                                                ) );
                                        }
                                        catch ( contradiction & con )
                                        { pt.join( con.pt ); }
                                    }
                                    else
                                    {
                                        try_insert( sequent, l, false );
                                        try_insert( sequent, r, false );
                                    }
                                } ),
                            make_not_actor(
                                [&]( const free_sentence & sen )
                                { try_insert( sequent, sen, ! t.second ); } )
                        );
                    }
                    catch ( contradiction & con )
                    {
                        leaf.join( con.pt );
                        return validity::valid;
                    }
                    leaf = leaf.join( proof_tree( static_cast< std::string >( * this ) ) );
                }
                return std::experimental::optional< validity >( );
            }
            validity is_valid( )
            {
                pt = proof_tree( static_cast< std::string >( * this ) );
                proof_tree leaf = pt;
                while ( true )
                {
                    auto ret = expand( leaf );
                    if ( ret ) { return * ret; }
                }
            }
            sequence( const sequence & t ) :
                sequent( t.sequent ),
                temp_sequent( t.temp_sequent ),
                cv_map( t.cv_map ),
                term_map( t.term_map ),
                expanded( t.expanded ),
                unused( t.unused ),
                functions( t.functions ),
                predicates( t.predicates ),
                tg( this, 1, cv_map, functions ) { }
            sequence( const free_sentence & t ) :
                sequent( { { t, false } } ), tg( this, 1, cv_map, functions )
            {
                first_order_logic::functions( t, std::inserter( functions, functions.begin( ) ) );
                first_order_logic::predicates( t, std::inserter( predicates, predicates.begin( ) ) );
                cv
                (
                    t,
                    common::make_function_output_iterator(
                        [&]( const term & t )
                        { cv_map.insert( std::make_pair( t, std::set< free_sentence >( ) ) ); } )
                );
                term_map = cv_map;
                if ( cv_map.empty( ) ) { new_variable( ); }
                if ( have_equal( t ) ) { add_equal_generator( ); }
            }
        };
        static std::pair< proof_tree, validity > is_valid( free_sentence & te )
        {
            sequence t( te );
            return std::make_pair( t.pt, t.is_valid( ) );
        }
    };
}
#endif //FIRST_ORDER_LOGIC_FOL_GENTZEN_SYSTEM_HPP
