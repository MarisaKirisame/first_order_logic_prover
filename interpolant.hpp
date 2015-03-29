#ifndef INTERPOLANT_HPP
#define INTERPOLANT_HPP
#include "gentzen_system.hpp"
#include "function_output_iterator.hpp"
namespace first_order_logic
{
    proposition interpolant( const proposition & l, const proposition & r )
    {
        assert( gentzen_system::is_valid( make_imply( l, r ) ) );
        proposition ret( sub );
        std::set< std::string > var;
        l.variable( std::inserter( var, var.begin( ) ) );
        r.variable( make_function_output_iterator( [&]( const std::string & s ){ var.erase( s ); } ) );
        for ( const std::string & str : var )
        { ret = make_or( ret.subsitute( proposition( str ), make_true( ) ), ret.subsitute( proposition( str ), make_false( ) ) ); }
        assert( gentzen_system::is_valid( make_imply( l, ret ) ) );
        assert( gentzen_system::is_valid( make_imply( ret, r ) ) );
        return ret;
    }
}
#endif // INTERPOLANT_HPP
