#ifndef FIRST_ORDER_LOGIC_SENTENCE_CONSTANTS_HPP
#define FIRST_ORDER_LOGIC_SENTENCE_CONSTANTS_HPP
#include "constant.hpp"
namespace first_order_logic
{
    struct constant
    {
        std::string name;
        constant( const std::string & str ) : name( str ) { }
        template< typename T >
        explicit constant( const T & t ) : name( t ) { }
        explicit constant( ) { }
        explicit operator std::string( ) const { return name; }
        bool operator < ( const constant & comp ) const { return name < comp.name; }
    };
}
#endif //FIRST_ORDER_LOGIC_SENTENCE_CONSTANTS_HPP
