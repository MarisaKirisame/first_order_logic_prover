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
				return it == data.end( ) ? t : make_variable( it->second->name );
			}
			else if ( t->name == "constant" ) { return t; }
			else
			{
				std::vector< term > te;
				te.reserve( t->arguments.size( ) );
				std::transform( t->arguments.begin( ), t->arguments.end( ), std::back_inserter( te ), [&,this]( const term & ter ){ return (*this)( ter ); } );
				return term( t->name, te );
			}
		}
	};
	substitution unify( const term & p, const term & q, const substitution & sub )
	{

	}
	boost::optional< substitution > unify_variable( const std::string & var, const term & t, const substitution & sub )
	{
		{
			auto it = sub.data.find( var );
			if ( it != sub.data.end( ) )
			{ return unify( it->second, t, sub ); }
		}
		if ( t->name == "variable" )
		{
			assert( t->arguments.size( ) == 1 );
			auto it = sub.data.find( t->arguments[0]->name );
			if ( it != sub.data.end( ) ) { return unify( make_variable( var ), it->second, sub ); }
		}
		auto occur_check =
				[&]( const auto & self, const term & te )->bool
				{
					return
							std::any_of(
								te->arguments.begin( ),
								te->arguments.end( ),
								[&]( const term & te )
								{ return ( te->name == "variable" && te->arguments[0]->name == var ) || self( self, te );; } );
				};
		if ( occur_check( occur_check, t ) ) { return boost::optional< substitution >( ); }
		substitution ret;
		ret.data.insert( { var, t } );
		return ret;
	}
}
#endif // SUBSTITUTION_HPP
