#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "sentence.hpp"
#include <map>
#include <string>
#include "first_order_logic.hpp"
namespace first_order_logic
{
	/*struct substitution
	{
		std::map< variable, term > data;
		sentence operator ( )( const sentence & t ) const
		{
			throw t;
		}
	};
	substitution unify( const sentence & p, const sentence & q, const substitution & sub )
	{
		throw p;
		throw q;
		throw sub;
	}
	boost::optional< substitution > unify_variable( const std::string & var, const sentence & t, const substitution & sub )
	{
		{
			//auto it = sub.data.find( var );
			//if ( it != sub.data.end( ) )
			//{ return unify( it->second, t, sub ); }
		}
		if ( t->name == "variable" )
		{
			assert( t->arguments.size( ) == 1 );
			//auto it = sub.data.find( t->arguments[0]->name );
			//if ( it != sub.data.end( ) ) { return unify( make_variable( var ), it->second, sub ); }
		}
		auto occur_check =
				[&]( const auto & self, const sentence & te )->bool
				{
					return
							std::any_of(
								te->arguments.begin( ),
								te->arguments.end( ),
								[&]( const sentence & te )
								{ return ( te->name == "variable" && te->arguments[0]->name == var ) || self( self, te );; } );
				};
		//if ( occur_check( occur_check, t ) ) { return boost::optional< substitution >( ); }
		//substitution ret;
		//ret.data.insert( { var, t } );
		//return ret;
	}*/
}
#endif // SUBSTITUTION_HPP
