#ifndef FIRST_ORDER_LOGIC_SENTENCE_TERM_HPP
#define FIRST_ORDER_LOGIC_SENTENCE_TERM_HPP
#include <cassert>
#include "../cpp_common/iterator.hpp"
#include "function.hpp"
#include <vector>
#include <memory>
#include <algorithm>
#include <set>
#include "variable.hpp"
#include "constant.hpp"
#include <numeric>
namespace first_order_logic
{
    struct term
    {
        enum class type { function, constant, variable };
        struct internal
        {
            type term_type;
            std::string name;
            mutable std::string cache;
            std::vector< term > arguments;
            internal( type term_type, const std::string & name, const std::vector< term > & arguments ) :
                term_type( term_type ), name( name ), arguments( arguments ) { }
        };
        std::shared_ptr< internal > data;
        explicit term( type term_type, const std::string & name, const std::vector< term > & arguments ) :
            data( new internal( term_type, name, arguments ) ) { }
        explicit term( const std::shared_ptr< internal > & data ) : data( data ) { }
        template< typename OUTITER >
        OUTITER constants( OUTITER result ) const
        {
            switch ( (*this)->term_type )
            {
                case type::variable:
                    return result;
                case type::constant:
                    *result = constant( (*this)->name );
                    ++result;
                    return result;
                case type::function:
                {
                    for ( const term & t : (*this)->arguments ) { result = t.constants( result ); }
                    return result;
                }
            }
            throw std::invalid_argument( "unknown enum type" );
        }
        size_t length( ) const
        {
            return
                    std::accumulate
                    (
                        (*this)->arguments.begin( ),
                        (*this)->arguments.end( ),
                        1,
                        []( size_t s, const term & t ){ return s + t.length( ); } );
        }
        template< typename OUTITER >
        OUTITER variables( OUTITER result ) const
        {
            switch ( (*this)->term_type )
            {
                case type::variable:
                    *result = variable( (*this)->name );
                    ++result;
                    return result;
                case type::constant:
                    return result;
                case type::function:
                {
                    for ( const term & t : (*this)->arguments )
                    { result = t.variables( result ); }
                    return result;
                }
            }
            throw std::invalid_argument( "unknown enum type" );
        }
        template< typename OUTITER >
        OUTITER functions( OUTITER result ) const
        {
            if ( (*this)->term_type == type::function )
            {
                * result = function( (*this)->name, (*this)->arguments.size( ) );
                ++result;
            }
            for( const term & t : (*this)->arguments ) { result = t.functions( result ); }
            return result;
        }
        const internal * operator -> ( ) const { return data.get( ); }
        explicit operator std::string( ) const
        {
            if ( ! (*this)->cache.empty( ) ) { return (*this)->cache; }
            assert( data );
            std::string stack;
            auto it = (*this)->arguments.begin( );
            while ( it != (*this)->arguments.end( ) )
            {
                if ( it != (*this)->arguments.begin( ) ) { stack += ", "; }
                assert( it->data );
                stack += static_cast< std::string >( * it );
                ++it;
            }
            (*this)->cache = (*this)->name + ( stack.empty( ) ? "" : "(" + stack + ")" );
            return (*this)->cache;
        }
        bool operator < ( const term & comp ) const
        { return static_cast< std::string >( * this ) < static_cast< std::string >( comp ); }
        bool operator == ( const term & comp ) const
        { return static_cast< std::string >( * this ) == static_cast< std::string >( comp ); }
        bool operator != ( const term & comp ) const
        { return static_cast< std::string >( * this ) != static_cast< std::string >( comp ); }
        explicit term( ) { }
        explicit term( const variable & var ) : data( new internal( type::variable, var.name, { } ) ) { }
        explicit term( const constant & var ) : data( new internal( type::constant, var.name, { } ) ) { }
        template< typename OUTITER >
        OUTITER cv( OUTITER result ) const
        {
            switch ( (*this)->term_type )
            {
            case type::variable:
            case type::constant:
                * result = { term( data ) };
                ++result;
                return result;
            case type::function:
                {
                    std::for_each(
                            (*this)->arguments.begin( ),
                            (*this)->arguments.end( ),
                            [&]( const term & t ){ result = t.cv( result ); } );
                    return result;
                }
            }
            throw std::invalid_argument( "unknown enum type" );
        }
        template< typename OUTITER >
        OUTITER used_name( OUTITER result ) const
        {
            * result = (*this)->name;
            ++result;
            if ( (*this)->term_type == type::function )
            {
                std::for_each(
                        (*this)->arguments.begin( ),
                        (*this)->arguments.end( ),
                        [&]( const term & t ){ result = t.used_name( result ); } );
            }
            return result;
        }
    };
}
#endif //FIRST_ORDER_LOGIC_SENTENCE_TERM_HPP
