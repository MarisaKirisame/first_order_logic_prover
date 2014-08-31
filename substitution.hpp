#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "term.hpp"
#include <map>
#include <string>
#include "first_order_logic.hpp"
namespace first_order_logic
{
	struct substitution
	{
		std::map< std::string, term > data;
		term operator ( )( const term & t ) const
		{
			if ( t->name == "variable" )
			{
				assert( t->arguments.size( ) == 0 );
				auto it = data.find( t->arguments[0]->name );
				return it == data.end( ) ? t : make_variable( it->second );
			}
			else if ( t->name == "constant" ) { return term; }
			else if ( t->is_quantifier( ) )
			{
				assert( t->arguments.size( ) == 2 );
				assert( t->arguments[0]->name == "variable" );
				assert( t->arguments[0]->arguments.size( ) == 1 );
				auto it = data.find( t->arguments[0]->arguments[0]->name );
				return it == data.end( ) ? t : term( new term::internal( ( *this )( t->arguments[1] ) ) );
			}
			else
			{
				std::vector< term > te;
				te.reserve( t->arguments.size( ) );
				std::transform( t->arguments.begin( ), t->arguments.end( ), std::back_inserter( te ), [&,this]( const term & ter ){ return (*this)( ter ); } );
				return term( t->name, te );
			}
		}
	};
}
#endif // SUBSTITUTION_HPP
