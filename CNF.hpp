#ifndef CNF_HPP
#define CNF_HPP
#include "atomic_sentence.hpp"
#include <list>
namespace first_order_logic
{
    template< typename t >
    struct conjunction
    {
        std::list< t > data;
        conjunction( std::initializer_list< t > d ) : data( d ) { }
        conjunction( std::list< t > && d ) : data( std::move( d ) ) { }
        conjunction( ) { }
    };
    template< typename t >
    struct disjunction
    {
        std::list< t > data;
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
        disjunction( const std::list< t > & d ) : data( d ) { }
        disjunction( std::list< t > && d ) : data( std::move( d ) ) { }
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
}
#endif // CNF_HPP
