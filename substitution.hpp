#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "sentence.hpp"
#include <map>
#include <string>
#include "forward/first_order_logic.hpp"
#include "algorithm"
#include <boost/optional.hpp>
#include "sentence.hpp"
#include "atomic_sentence.hpp"
#include "../misc/combinator.hpp"
namespace first_order_logic
{
    template< typename T, typename OUTITER >
    OUTITER free_variables( const sentence< T > & self, OUTITER result );
    template< typename OUTITER >
    OUTITER free_variables( const atomic_sentence & self, OUTITER result );
    struct substitution
    {
        std::map< variable, term > data;
        term operator ( )( const term & t ) const;
        inline atomic_sentence operator ( )( const atomic_sentence & as ) const;
        template< typename T >
        sentence< T > operator ( )( const sentence< T > & s ) const;
        substitution( const std::map< variable, term > & data ) : data( data ) { }
        substitution( ) { }
        bool operator ==( const substitution & s ) const { return data == s.data; }
        bool coherent( const substitution & comp ) const;
        static boost::optional< substitution > join( const substitution & l, const substitution & r );
    };
    template< typename T >
    boost::optional< substitution > unify(
            const sentence< T > & p, const atomic_sentence & q, const substitution & sub );
    template< typename T >
    boost::optional< substitution > unify(
            const atomic_sentence & p, const sentence< T > & q, const substitution & sub );
    boost::optional< substitution > unify(
            const term & p, const term & q, const substitution & sub );
    boost::optional< substitution > unify(
            const std::vector< term > & p, const std::vector< term > & q, const substitution & sub );
    boost::optional< substitution > unify(
            const variable & var, const term & t, const substitution & sub );
    boost::optional< substitution > unify(
            const term & p, const term & q, const substitution & sub );
    boost::optional< substitution > unify(
            const variable & var, const term & t, const substitution & sub );
    template< typename T >
    boost::optional< substitution > unify(
            const sentence< T > & p, const sentence< T > & q, const substitution & sub );
    boost::optional< substitution > unify(
            const atomic_sentence & p, const atomic_sentence & q, const substitution & sub );
    template< typename F, typename GENERATOR >
    void rename_variable( const term & t, const F & usable, const GENERATOR & gen, substitution & renamed );
    template< typename F, typename GENERATOR >
    void rename_variable(
            const variable & sen, const F & usable, const GENERATOR & gen, substitution & renamed );
    template< typename F, typename T, typename GENERATOR >
    void rename_variable(
            const sentence< T > & sen,
            const F & usable,
            const GENERATOR & gen,
            substitution & renamed );
    template< typename INITER, typename F, typename GENERATOR >
    void rename_variable(
            INITER begin,
            INITER end,
            const F & usable,
            const GENERATOR & gen,
            substitution & renamed );
    template< typename ... T >
    boost::optional< substitution > unify( const T & ... );
    template< typename ... T >
    substitution rename_variable( const T & ... );
    atomic_sentence substitution::operator ( )( const atomic_sentence & as ) const
    {
        return as.type_restore_full< atomic_sentence >
                (
                    make_equal_actor(
                        [&]( const term & l, const term & r )
                        { return make_equal( (*this)(l), (*this)(r) ); } ),
                    make_predicate_actor(
                        [&]( const std::string & str, const std::vector< term > & vec )
                        {
                            std::vector< term > tem;
                            std::transform(
                                vec.begin( ),
                                vec.end( ),
                                std::back_inserter( tem ),
                                [&]( const term & te ){ return(*this)(te); } );
                            return make_predicate( str, tem );
                        } ),
                    make_propositional_letter_actor(
                        [&]( const std::string & str ){ return make_propositional_letter( str ); } )
                );
    }
    inline term substitution::operator ( )( const term & t ) const
    {
        switch ( t->term_type )
        {
            case term::type::constant:
                return t;
            case term::type::variable:
            {
                auto it = data.find( t->name );
                return it == data.end( ) ? t : it->second;
            }
            case term::type::function:
            {
                std::vector< term > tem;
                std::transform(
                    t->arguments.begin( ),
                    t->arguments.end( ),
                    std::back_inserter( tem ),
                    [&]( const term & te ){ return(*this)(te); } );
                return make_function( t->name, tem );
            }
        }
        throw std::invalid_argument( "unknown enum type" );
    }
    template< typename T >
    sentence< T > substitution::operator ( )( const sentence< T > & s ) const
    {
        sentence< T > ret =
            s.template type_restore_full< sentence< T > >
            (
                make_all_actor(
                    [&]( const variable & var, const auto & sen )
                    {
                        auto it = data.find( var );
                        return ( it != data.end( ) ) ? make_all( var, sen ) : make_all( var, (*this)(sen) );
                    } ),
                make_some_actor(
                    [&]( const variable & var, const auto & sen )
                    {
                        auto it = data.find( var );
                        return ( it != data.end( ) ) ? make_some( var, sen ) : make_some( var, (*this)(sen) );
                    } ),
                make_and_actor(
                        [&]( const auto & l, const auto & r )
                        { return make_and( (*this)(l), (*this)(r) ); } ),
                make_or_actor(
                        [&]( const auto & l, const auto & r )
                        { return make_or( (*this)(l), (*this)(r) ); } ),
                make_not_actor(
                        [&]( const auto & sen ) { return make_not( (*this)(sen) ); } ),
                make_atomic_actor(
                        [&]( const atomic_sentence & sen ) { return sentence< T >( (*this)( sen ) ); } )
            );
        assert( ret.data );
        return ret;
    }
    inline bool substitution::coherent( const substitution & comp ) const
    {
        return std::any_of(
                    comp.data.begin( ),
                    comp.data.end( ),
                    [&]( const std::pair< variable, term > & p )
        {
            auto it = data.find( p.first );
            return it == data.end( ) && it->second == p.second;
        } );
    }
    inline boost::optional< substitution > substitution::join(
            const substitution & l, const substitution & r )
    {
        if ( l.data.size( ) > r.data.size( ) ) { return join( r, l ); }
        substitution ret( r );
        for ( const std::pair< variable, term > & i : l.data )
        {
            auto it = ret.data.insert( i );
            if ( it.first->first != i.first ) { return boost::optional< substitution >( ); }
        }
        return ret;
    }
    inline boost::optional< substitution > unify(
            const std::vector< term > & p, const std::vector< term > & q, const substitution & sub )
    {
        substitution ret( sub );
        assert( p.size( ) == q.size( ) );
        for ( size_t i = 0; i < p.size( ); ++i )
        {
            boost::optional< substitution > tem = unify( p[i], q[i], ret );
            if ( tem )
            {
                std::copy(
                    tem->data.begin( ),
                    tem->data.end( ),
                    std::inserter( ret.data, ret.data.begin( ) ) );
            }
            else { return boost::optional< substitution >( ); }
        }
        return ret;
    }
    inline boost::optional< substitution > unify( const term & p, const term & q, const substitution & sub )
    {
        if ( p->term_type != term::type::variable && q->term_type == term::type::variable )
        { return unify( q, p, sub ); }
        switch ( p->term_type )
        {
        case term::type::constant:
            return p == q ? sub : boost::optional< substitution >( );
        case term::type::variable:
            return unify( variable( p->name ), q, sub );
        case term::type::function:
            if ( p->term_type == q->term_type && p->name == q->name )
            { return unify( p->arguments, q->arguments, sub ); }
            return boost::optional< substitution >( );
        }
        throw std::invalid_argument( "unknown enum type." );
    }
    inline boost::optional< substitution > unify(
            const variable & var, const term & t, const substitution & sub )
    {
        {
            auto it = sub.data.find( var );
            if ( it != sub.data.end( ) )
            { return unify( it->second, t, sub ); }
        }
        if ( t->term_type == term::type::variable )
        {
            auto it = sub.data.find( t->name );
            if ( it != sub.data.end( ) ) { return unify( var, it->second, sub ); }
        }
        if ( t->term_type == term::type::variable && t->name == var.name ) { return sub; }
        auto occur_check =
            [&]( )
            {
                return
                    var.name == t->name ||
                    misc::fix(
                        [&]( const auto & self, const variable & var, const term & t )->bool
                        {
                            switch ( t->term_type )
                            {
                                case term::type::variable:
                                    return var.name != t->name;
                                case term::type::constant:
                                    return true;
                                case term::type::function:
                                    return std::all_of(
                                        t->arguments.begin( ),
                                        t->arguments.end( ),
                                        [&]( const term & te ) { return self( var, te ); } );
                            }
                            throw std::invalid_argument( "unknown enum type." );
                        } )( var, t );
            };
        if ( ! occur_check( ) ) { return boost::optional< substitution >( ); }
        substitution ret( sub );
        auto it = ret.data.insert( { var, t } );
        return it.first->second == t ? ret : boost::optional< substitution >( );
    }
    inline boost::optional< substitution > unify(
            const atomic_sentence & p, const atomic_sentence & q, const substitution & sub )
    {
        if ( p->atomic_sentence_type != q->atomic_sentence_type || p->name != q->name )
        { return boost::optional< substitution >( ); }
        return p.type_restore_full< boost::optional< substitution > >(
            make_predicate_actor(
                [&]( const std::string &, const std::vector< term > & ter )
                {
                    boost::optional< substitution > ret;
                    q.type_restore< void >(
                        make_predicate_actor(
                            [&]( const std::string &, const std::vector< term > & te )
                            {
                                assert( ter.size( ) == te.size( ) );
                                ret = sub;
                                for ( size_t i = 0; i < te.size( ); ++i )
                                {
                                    if ( ret ) { ret = unify( ter[i], te[i], * ret ); }
                                    else { break; }
                                }
                            } ),
                        error< >( ) );
                    return ret;
                } ),
            make_propositional_letter_actor(
                [&]( const std::string & ){ return boost::optional< substitution >( sub ); } ),
            make_equal_actor(
                [&]( const term & l, const term & r )
                {
                    boost::optional< substitution > ret;
                    q.type_restore< void >(
                        make_equal_actor(
                            [&]( const term & ll, const term & rr )
                            {
                                auto tem = unify( l, ll, sub );
                                if ( tem ) { ret = unify( r, rr, * tem ); }
                            } ),
                        error< >( ) );
                    return ret;
                } ) );
    }
    template< typename T >
    boost::optional< substitution > unify(
            const sentence< T > & p, const atomic_sentence & q, const substitution & sub )
    {
        boost::optional< atomic_sentence > as;
        p.type_restore( make_atomic_actor(
                            [&]( const atomic_sentence & asen ) { as = asen; } ), error< >( ) );
        return as ? unify( * as, q, sub ) : boost::optional< substitution >( );
    }
    template< typename T >
    boost::optional< substitution > unify(
            const atomic_sentence & p, const sentence< T > & q, const substitution & sub )
            { return unify( q, p, sub ); }
    template< typename T >
    boost::optional< substitution > unify(
            const sentence< T > & p, const sentence< T > & q, const substitution & sub )
    {
        if ( p->sentence_type != q->sentence_type || p->name != q->name )
        { return boost::optional< substitution >( ); }
        return p.type_restore_full(
                    make_all_actor(
                        [&]( const variable & var, const sentence< T > & sen )
                        {
                            boost::optional< substitution > ret;
                            q.type_restore(
                                make_all_actor(
                                    [&]( const variable & va, const sentence< T > & se )
                                    {
                                        ret = unify(
                                                substitution( { { va, term( var ) } } )( se ),
                                                sen,
                                                sub ); } ),
                                error< >( ) );
                            return ret;
                        } ),
                    make_some_actor(
                        [&]( const variable & var, const sentence< T > & sen )
                        {
                            boost::optional< substitution > ret;
                            q.type_restore(
                                make_some_actor(
                                    [&]( const variable & va, const sentence< T > & se )
                                    {
                                        ret = unify(
                                                    substitution( { { va, term( var ) } } )( se ),
                                                    sen,
                                                    sub );
                                    } ),
                                error< >( ) );
                            return ret;
                        } ),
                    make_and_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        {
                            boost::optional< substitution > ret;
                            q.type_restore(
                                make_and_actor(
                                    [&]( const sentence< T > & ll, const sentence< T > & rr )
                                    {
                                        auto tem = unify( l, ll, sub );
                                        if ( tem ) { ret = unify( r, rr, * tem ); }
                                    } ),
                                error< >( ) );
                            return ret;
                        } ),
                    make_or_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        {
                            boost::optional< substitution > ret;
                            q.type_restore(
                                make_or_actor(
                                    [&]( const sentence< T > & ll, const sentence< T > & rr )
                                    {
                                        auto tem = unify( l, ll, sub );
                                        if ( tem ) { ret = unify( r, rr, * tem ); }
                                    } ),
                                error< >( ) );
                            return ret;
                        } ),
                    make_not_actor(
                        [&]( const sentence< T > & sen )
                        {
                            boost::optional< substitution > ret;
                            q.type_restore(
                                make_not_actor(
                                    [&]( const sentence< T > & s ){ ret = unify( sen, s, sub ); } ),
                                error< >( ) );
                            return ret;
                        } ),
                    make_atomic_actor(
                        [&]( const atomic_sentence & as1 )
                        {
                            boost::optional< substitution > ret;
                            q.type_restore(
                                make_atomic_actor(
                                    [&]( const atomic_sentence & as2 ){ ret = unify( as1, as2, sub ); } ),
                                error< >( ) );
                            return ret;
                        } ) );
    }
    template< typename F, typename GENERATOR >
    void rename_variable( const term & t, const F & usable, const GENERATOR & gen, substitution & renamed )
    {
        switch ( t->term_type )
         {
            case term::type::variable:
                rename_variable( variable( t->name ), usable, gen, renamed );
            case term::type::constant:
                break;
            case term::type::function:
                rename_variable( t->arguments.begin( ), t->arguments.end( ), usable, gen, renamed );
        }
    }
    template< typename F, typename GENERATOR >
    void rename_variable(
            const variable & sen, const F & usable, const GENERATOR & gen, substitution & renamed )
    {
        std::string gen_str = sen.name;
        while ( renamed.data.count( gen_str ) != 0 || ! usable( gen_str ) ) { gen_str = gen( gen_str ); }
        if ( gen_str != sen.name )
        {
            renamed.data.insert( std::make_pair(
                                     variable( sen.name ),
                                     make_variable( gen_str ) ) ); }
    }
    template< typename F, typename T, typename GENERATOR >
    void rename_variable(
            const sentence< T > & sen, const F & usable, const GENERATOR & gen, substitution & renamed )
    {
        std::set< variable > tem;
        free_variables( sen, std::inserter( tem, tem.begin( ) ) );
        rename_variable( tem.begin( ), tem.end( ), usable, gen, renamed );
    }
    template< typename F, typename GENERATOR >
    void rename_variable(
            const atomic_sentence & sen, const F & usable, const GENERATOR & gen, substitution & renamed )
    {
        std::set< variable > tem;
        free_variables( sen, std::inserter( tem, tem.begin( ) ) );
        rename_variable( tem.begin( ), tem.end( ), usable, gen, renamed );
    }
    template< typename INITER, typename F, typename GENERATOR >
    void rename_variable(
            INITER begin, INITER end, const F & usable, const GENERATOR & gen, substitution & renamed )
    {
        std::for_each(
            begin,
            end,
            [&]( const auto & te ){ rename_variable( te, usable, gen, renamed ); } );
    }
    template< typename ... T >
    substitution rename_variable( const T & ... t )
    {
        static_assert(
            ! std::is_same
            <
                typename
                    std::tuple_element
                    <
                        std::tuple_size< std::tuple< T ... > >::value - 1,
                        std::tuple< T ... >
                    >::type,
                substitution
            >::value,
            "Recursive call detected. Possibly result from invalid argument(s)." );
        substitution ret;
        rename_variable( t ..., ret );
        return ret;
    }
    template< typename ... T >
    boost::optional< substitution > unify( const T & ... t )
    {
        static_assert(
            ! std::is_same
            <
                typename
                    std::tuple_element
                    <
                        std::tuple_size< std::tuple< T ... > >::value - 1,
                        std::tuple< T ... >
                    >::type,
                substitution
            >::value,
            "Recursive call detected. Possibly result from invalid argument(s)." );
        return unify( t ..., substitution( ) );
    }
}
#endif // SUBSTITUTION_HPP
