#ifndef VARIABLE_HPP
#define VARIABLE_HPP
#include "term.hpp"
#include <string>
namespace first_order_logic
{
	struct variable
	{
		std::string name;
		variable( const std::string & str ) : name( str ) { }
		template< typename T >
		variable( const T & t ) : name( t ) { }
		variable( ) { }
		explicit operator std::string( ) const { return name; }
		bool operator < ( const variable & comp ) const { return name < comp.name; }
		bool operator != ( const variable & comp ) const { return name != comp.name; }
	};
}
#endif // VARIABLE_HPP
