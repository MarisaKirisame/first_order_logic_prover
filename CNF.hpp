#ifndef CNF_HPP
#define CNF_HPP
#include "sentence.hpp"
#include <list>
#include <set>
#include <iterator>
#include <algorithm>
#include <boost/iterator/transform_iterator.hpp>
namespace first_order_logic
{
    typedef sentence
    <
        vector
        <
            set_c
            <
                sentence_type,
                sentence_type::logical_and,
                sentence_type::logical_or,
                sentence_type::logical_not
            >
        >
    > free_propositional_sentence;
    static_assert(
        free_propositional_sentence::full_type_restore
        <
            and_actor< common::error< > >,
            or_actor< common::error< > >,
            not_actor< common::error< > >,
            atomic_actor< common::error< > >
        >::value,
        "type missing" );
    typedef
    sentence
    <
        vector
        <
            set_c
            <
                sentence_type,
                sentence_type::logical_and,
                sentence_type::logical_or
            >,
            set_c< sentence_type, sentence_type::logical_not >
        >
    > negation_in_type;
    negation_in_type move_negation_in( const free_propositional_sentence & prop )
    {
        return prop.type_restore_full< negation_in_type >
                (
                    make_not_actor(
                        [&]( const free_propositional_sentence & sen )
                        {
                            return sen.type_restore_full< negation_in_type >(
                                    make_not_actor(
                                            [&]( const free_propositional_sentence & sen )
                                            { return move_negation_in( sen ); } ),
                                    make_and_actor(
                                            [&]( const free_propositional_sentence & l,
                                                 const free_propositional_sentence & r )
                                            {
                                                return make_or(
                                                    move_negation_in( make_not( l ) ),
                                                    move_negation_in( make_not( r ) ) );
                                            } ),
                                    make_or_actor(
                                        [&]( const free_propositional_sentence & l,
                                             const free_propositional_sentence & r )
                                        {
                                            return make_and(
                                                move_negation_in( make_not( l ) ),
                                                move_negation_in( make_not( r ) ) );
                                        } ),
                                    make_atomic_actor( []( const atomic_sentence & as ) { return make_not( as ); } ) );
                        } ),
                    make_and_actor(
                        [&]( const free_propositional_sentence & l, const free_propositional_sentence & r )
                            { return make_and( move_negation_in( l ), move_negation_in( r ) ); } ),
                    make_or_actor(
                        [&]( const free_propositional_sentence & l, const free_propositional_sentence & r )
                            { return make_or( move_negation_in( l ), move_negation_in( r ) ); } ),
                    make_atomic_actor( []( const atomic_sentence & as ) { return as; } ) );
    }
    typedef
    sentence
    <
        vector
        <
            set_c< sentence_type, sentence_type::logical_and >,
            set_c< sentence_type, sentence_type::logical_or >,
            set_c< sentence_type, sentence_type::logical_not >
        >
    > and_or_not_type;
    typedef
    sentence
    <
        vector
        <
            set_c< sentence_type, sentence_type::logical_or >,
            set_c< sentence_type, sentence_type::logical_and >,
            set_c< sentence_type, sentence_type::logical_or >,
            set_c< sentence_type, sentence_type::logical_not >
        >
    > or_and_or_not_type;
    typedef
    sentence
    <
        vector
        <
            set_c< sentence_type, sentence_type::logical_or >,
            set_c< sentence_type, sentence_type::logical_not >
        >
    > or_not_type;
    typedef sentence< vector < set_c< sentence_type, sentence_type::logical_not > > > not_type;
    static_assert( std::is_convertible< or_and_or_not_type, negation_in_type >::value, "should be convertible" );
    static_assert( std::is_convertible< not_type, free_propositional_sentence >::value, "should be convertible" );
    static_assert( std::is_convertible< or_not_type, and_or_not_type >::value, "should be convertible" );
    static_assert( std::is_same< and_or_not_type::not_sentence_type, not_type >::value, "should be same" );
    static_assert(
        ! have< current_set< negation_in_type >::type, set_c< sentence_type, sentence_type::logical_not > >::value,
        "should not have or" );
    and_or_not_type move_or_in( const negation_in_type & prop )
    {
        return prop.type_restore_full< and_or_not_type >(
                make_not_actor( []( const not_type & sen )->and_or_not_type { return make_not( sen ); } ),
                make_and_actor(
                    []( const negation_in_type & l, const negation_in_type & r )
                        { return make_and( move_or_in( l ), move_or_in( r ) ); } ),
                make_or_actor(
                    []( const negation_in_type & l, const negation_in_type & r )
                        {
                            auto switch_process =
                                [&]( const or_not_type & as )->and_or_not_type
                                {
                                    return move_or_in( r ).type_restore_full< and_or_not_type >(
                                        make_and_actor(
                                            [&]( const and_or_not_type & ll, const and_or_not_type & rr )
                                            {
                                                return make_and(
                                                    move_or_in( make_or( as, ll ) ),
                                                    move_or_in( make_or( as, rr ) ) );
                                            } ),
                                        make_or_actor(
                                            [&]( const or_not_type & ll, const or_not_type & rr )
                                            { return make_or( as, make_or( ll, rr ) ); } ),
                                        make_not_actor(
                                            [&]( const not_type & s )
                                            { return make_or( as, make_not( s ) ); } ),
                                        make_atomic_actor(
                                            [&]( const atomic_sentence & s )
                                            { return make_or( as, s ); } ) );
                                };
                            return move_or_in( l ).template type_restore_full< and_or_not_type >(
                                make_and_actor(
                                    [&]( const and_or_not_type & ll, const and_or_not_type & rr )
                                    {
                                        return make_and(
                                            move_or_in( make_or( r, ll ) ),
                                            move_or_in( make_or( r, rr ) ) );
                                    } ),
                                make_or_actor(
                                    [&]( const or_not_type & ll, const or_not_type & rr )
                                    { return switch_process( make_or( ll, rr ) ); } ),
                                make_not_actor(
                                    [&]( const not_type & s ) { return switch_process( make_not( s ) ); } ),
                                make_atomic_actor(
                                    [&]( const atomic_sentence & as ) { return switch_process( as ); } ) );
                        } ),
                make_atomic_actor( []( const atomic_sentence & as ) { return as; } ) );
    }

    struct literal
    {
        atomic_sentence as;
        bool b;
        literal( const atomic_sentence & as, bool b ) : as( as ), b( b ) { }
        bool operator < ( const literal & cmp ) const { return std::tie( as, b ) < std::tie( cmp.as, cmp.b );}
        bool operator == ( const literal & cmp ) const { return std::tie( as, b ) == std::tie( cmp.as, cmp.b );}
        bool operator != ( const literal & cmp ) const { return std::tie( as, b ) != std::tie( cmp.as, cmp.b );}
        bool operator > ( const literal & cmp ) const { return std::tie( as, b ) > std::tie( cmp.as, cmp.b );}
        bool operator >= ( const literal & cmp ) const { return std::tie( as, b ) <= std::tie( cmp.as, cmp.b );}
        bool operator <= ( const literal & cmp ) const { return std::tie( as, b ) >= std::tie( cmp.as, cmp.b );}
    };

    literal get_literal( const not_type & nt )
    {
        return nt.type_restore_full< literal >(
                make_not_actor(
                    []( const not_type & n )
                    {
                        literal ret = get_literal( n );
                        ret.b = ! ret.b;
                        return ret;
                    } ),
                make_atomic_actor( []( const atomic_sentence & as ) { return literal( as, true ); } ) );
    }

    template< typename OUTITER >
    OUTITER get_clause( const or_not_type & prop, OUTITER result )
    {
        return
            prop.type_restore_full< OUTITER >
            (
                make_or_actor(
                    [&]( const or_not_type & l, const or_not_type & r )
                        { return get_clause( l, get_clause( r, result ) ); } ),
                make_not_actor(
                    [&]( const not_type & sen )
                    {
                        literal l = get_literal( sen );
                        l.b = ! l.b;
                        * result = l;
                        ++result;
                        return result;
                    } ),
                make_atomic_actor(
                    [&]( const atomic_sentence & as )
                    {
                        * result = literal( as, true );
                        ++result;
                        return result;
                    } )
            );
    }

    template< typename OUTITER >
    OUTITER get_cnf( const and_or_not_type & prop, OUTITER result )
    {
        auto extract_clause =
            [&]( const or_not_type & t )
            {
                result = get_clause( t, result );
                * result = boost::optional< literal >( );
                ++result;
                return result;
            };
        return prop.type_restore_full< OUTITER >(
                make_and_actor(
                    [&]( const and_or_not_type & l, const and_or_not_type & r )
                    { return get_cnf( l, get_cnf( r, result ) ); } ),
                make_not_actor( [&]( const not_type & l ) { return extract_clause( make_not( l ) ); } ),
                make_or_actor(
                    [&]( const or_not_type & l, const or_not_type & r )
                    { return extract_clause( make_or( l, r ) ); } ),
                make_atomic_actor( [&]( const atomic_sentence & as ) { return extract_clause( as ); } ) );
    }

    and_or_not_type pre_CNF( const free_propositional_sentence & prop )
    { return move_or_in( move_negation_in( prop ) ); }

    template< typename OUTITER >
    OUTITER to_CNF( const free_propositional_sentence & prop, OUTITER out )
    { return get_cnf( pre_CNF( prop ), out ); }

    std::list< std::list< literal > > list_list_literal( const free_propositional_sentence & sen )
    {
        std::list< std::list< literal > > CNF;
        std::list< literal > builder;
        to_CNF(
            sen,
            make_function_output_iterator(
                [&]( const boost::optional< literal > & bl )
                {
                    if ( bl ) { builder.push_back( bl.get( ) ); }
                    else
                    {
                        std::list< literal > tem;
                        std::swap( tem, builder );
                        CNF.push_back( std::move( tem ) );
                    }
                } ) );
        return CNF;
    }

    std::set< std::set< literal > > set_set_literal( const free_propositional_sentence & sen )
    {
        std::set< std::set< literal > > CNF;
        std::set< literal > builder;
        to_CNF(
            sen,
        make_function_output_iterator(
            [&]( const boost::optional< literal > & bl )
            {
                if ( bl ) { builder.insert( bl.get( ) ); }
                else
                {
                    std::set< literal > tem;
                    std::swap( tem, builder );
                    CNF.insert( std::move( tem ) );
                }
            } ) );
        return CNF;
    }

    template< typename T >
    std::list< T > set_to_list( const std::set< T > & c ) { return std::list< T >( c.begin( ), c.end( ) ); }

    template< typename T >
    std::set< T > list_to_set( const std::list< T > & c ) { return std::set< T >( c.begin( ), c.end( ) ); }

    template< typename T >
    std::list< std::list< T > > set_set_to_list_list( const std::set< std::set< T > > & c )
    {
        auto f = []( const std::set< T > & c ) { return set_to_list( c ); };
        return std::list< std::list< T > >( boost::make_transform_iterator( c.begin( ), f ), boost::make_transform_iterator( c.end( ), f ) );
    }

    template< typename T >
    std::set< std::set< T > > list_list_to_set_set( const std::list< std::list< T > > & c )
    {
        auto f = []( const std::list< T > & c ) { return list_to_set( c ); };
        return std::set< std::set< T > >( boost::make_transform_iterator( c.begin( ), f ), boost::make_transform_iterator( c.end( ), f ) );
    }
}
#endif // CNF_HPP
