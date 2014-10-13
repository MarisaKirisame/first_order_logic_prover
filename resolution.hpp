#ifndef RESOLUTION_HPP
#define RESOLUTION_HPP
#include "sentence.hpp"
#include "term.hpp"
#include "TMP.hpp"
namespace first_order_logic
{
    template< typename t >
    struct conjunction
    {
        std::set< t > data;
        conjunction( std::initializer_list< t > d ) : data( d ) { }
        conjunction( std::set< t > && d ) : data( std::move( d ) ) { }
        conjunction( ) { }
    };
    template< typename t >
    struct disjunction
    {
        std::set< t > data;
        disjunction( std::initializer_list< t > d ) : data( d ) { }
        disjunction( ) { }
        bool operator < ( const disjunction & comp ) const { return data < comp.data; }
        bool operator == ( const disjunction & comp ) const { return data == comp.data; }
        struct join_faliure { };
        disjunction join( const disjunction & d ) const
        {
            if ( & d == this ) { throw join_faliure( ); }
            assert( d.data.size( ) < 1000 );
            assert( data.size( ) < 1000 );
            if ( d.data.size( ) < data.size( ) ) { return d.join( * this ); }
            std::set< t > conjugate_set;
            for ( auto i : data )
            {
                auto con = i.conjugate( );
                assert( d.data.size( ) < 1000 );
                assert( data.size( ) < 1000 );
                if ( d.data.find( con ) != d.data.end( ) )
                { conjugate_set.insert( i ); }
            }
            if ( conjugate_set.size( ) != 1 ) { join_faliure jf; throw jf; }
            else
            {
                disjunction ret( d.data );
                std::copy( data.begin( ), data.end( ), std::inserter( ret.data, ret.data.begin( ) ) );
                ret.data.erase( * conjugate_set.begin( ) );
                ret.data.erase( conjugate_set.begin( )->conjugate( ) );
                return ret;
            }
        }
        disjunction( const std::set< t > & d ) : data( d ) { }
        disjunction( std::set< t > && d ) : data( std::move( d ) ) { }
    };
    struct literal
    {
        atomic_sentence data;
        bool b;
        literal( const atomic_sentence & d, bool b ) : data( d ), b( b ) { }
        bool operator < ( const literal & comp ) const { return std::tie( data, b ) < std::tie( comp.data, comp.b ); }
        bool operator == ( const literal & comp ) const { return std::tie( data, b ) == std::tie( comp.data, comp.b ); }
        literal conjugate( ) const
        {
            literal ret( * this );
            ret.b = ! ret.b;
            return ret;
        }
    };
    typedef disjunction< literal > clause;
    typedef conjunction< clause > CNF;
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
            and_actor< error< > >,
            or_actor< error< > >,
            not_actor< error< > >,
            atomic_actor< error< > >
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
                                            [&]( const free_propositional_sentence & l, const free_propositional_sentence & r )
                                            {
                                                return make_or(
                                                    move_negation_in( make_not( l ) ),
                                                    move_negation_in( make_not( r ) ) );
                                            } ),
                                    make_or_actor(
                                        [&]( const free_propositional_sentence & l, const free_propositional_sentence & r )
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
    OUTITER flatten( const and_or_not_type & prop, OUTITER result )
    {
        auto extract_clause =
            [&]( const or_not_type & t )
            {
                clause cl;
                get_clause( t, std::inserter( cl.data, cl.data.begin( ) ) );
                * result = cl;
                ++result;
                return result;
            };
        return prop.type_restore_full< OUTITER >(
                make_and_actor(
                    [&]( const and_or_not_type & l, const and_or_not_type & r )
                    { return flatten( l, flatten( r, result ) ); } ),
                make_not_actor( [&]( const not_type & l ) { return extract_clause( make_not( l ) ); } ),
                make_or_actor(
                    [&]( const or_not_type & l, const or_not_type & r )
                    { return extract_clause( make_or( l, r ) ); } ),
                make_atomic_actor( [&]( const atomic_sentence & as ) { return extract_clause( as ); } ) );
    }

    and_or_not_type pre_CNF( const free_propositional_sentence & prop )
    { return move_or_in( move_negation_in( prop ) ); }

    CNF to_CNF( const free_propositional_sentence & prop )
    {
        CNF ret;
        flatten( pre_CNF( prop ), std::inserter( ret.data, ret.data.begin( ) ) );
        return ret;
    }

    bool resolution( const free_sentence & sen, const free_sentence & goal )
    {
        CNF cnf(
                to_CNF(
                    make_and( sen, make_not( goal ).restore_quantifier_universal( ) ).
                    rectify( ).
                    move_quantifier_out( ).
                    skolemization_remove_existential( ).
                    drop_universal( ) ) );
        std::set< clause > to_be_added;
        bool have_new_inference = true;
        while ( have_new_inference )
        {
            have_new_inference = false;
            for ( const clause & l : cnf.data )
            {
                for ( const clause & r : cnf.data )
                {
                    for ( const literal & ll : l.data )
                    {
                        for ( const literal & rr : r.data )
                        {
                            if ( ll.b != rr.b )
                            {
                                auto un = unify( ll.data, rr.data );
                                if ( un )
                                {
                                    clause cl;
                                    for ( const literal & ins : l.data )
                                    {
                                        if ( (*un)(ins.data) != (*un)(ll.data) && (*un)(ins.data) != (*un)(rr.data) )
                                        { cl.data.insert( literal( (*un)( ins.data ), ins.b ) ); }
                                    }
                                    for ( const literal & ins : r.data )
                                    {
                                        if ( (*un)(ins.data) != (*un)(ll.data) && (*un)(ins.data) != (*un)(rr.data) )
                                        { cl.data.insert( literal( (*un)( ins.data ), ins.b ) ); }
                                    }
                                    if ( cl.data.empty( ) ) { return true; }
                                    to_be_added.insert( cl );
                                }
                            }
                        }
                    }
                }
            }
            for ( const clause & c : to_be_added )
            {
                auto res = cnf.data.insert( c );
                have_new_inference = have_new_inference || res.second;
            }
            to_be_added.clear( );
        }
        return false;
    }
}
#endif // RESOLUTION_HPP
