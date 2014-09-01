#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "atomic_sentence.hpp"
#include "complex_sentence.hpp"
#include <map>
#include <string>
#include "first_order_logic.hpp"
namespace first_order_logic
{
	struct substitution
	{
		std::map< std::string, atomic_sentence > data;
		atomic_sentence operator ( )( const atomic_sentence & t ) const
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
				std::vector< atomic_sentence > te;
				te.reserve( t->arguments.size( ) );
				std::transform( t->arguments.begin( ), t->arguments.end( ), std::back_inserter( te ), [&,this]( const atomic_sentence & ter ){ return (*this)( ter ); } );
				return atomic_sentence( t->name, te );
			}
		}
	};
	substitution unify( const atomic_sentence & p, const atomic_sentence & q, const substitution & sub )
	{

	}
	boost::optional< substitution > unify_variable( const std::string & var, const atomic_sentence & t, const substitution & sub )
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
				[&]( const auto & self, const atomic_sentence & te )->bool
				{
					return
							std::any_of(
								te->arguments.begin( ),
								te->arguments.end( ),
								[&]( const atomic_sentence & te )
								{ return ( te->name == "variable" && te->arguments[0]->name == var ) || self( self, te );; } );
				};
		if ( occur_check( occur_check, t ) ) { return boost::optional< substitution >( ); }
		substitution ret;
		ret.data.insert( { var, t } );
		return ret;
	}
}
#endif // SUBSTITUTION_HPP
