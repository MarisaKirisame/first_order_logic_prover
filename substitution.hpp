#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "sentence.hpp"
#include <map>
#include <string>
#include "first_order_logic.hpp"
#include "algorithm"
#include <boost/optional.hpp>
namespace first_order_logic
{
	struct substitution
	{
		std::map< variable, term > data;
		term operator ( )( const term & t ) const
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
		sentence operator ( )( const sentence & s ) const
		{
			return
				s.type_restore_full
				(
					make_all_actor(
						[&]( const variable & var, const sentence & sen )
						{
							auto it = data.find( var );
							return ( it != data.end( ) ) ? make_all( var, sen ) : make_all( var, (*this)(sen) );
						} ),
					make_some_actor(
						[&]( const variable & var, const sentence & sen )
						{
							auto it = data.find( var );
							return ( it != data.end( ) ) ? make_some( var, sen ) : make_some( var, (*this)(sen) );
						} ),
					make_and_actor( [&]( const sentence & l, const sentence & r ){ return make_and( (*this)(l), (*this)(r) ); } ),
					make_or_actor( [&]( const sentence & l, const sentence & r ){ return make_or( (*this)(l), (*this)(r) ); } ),
					make_not_actor( [&]( const sentence & sen ){ return make_not( (*this)(sen) ); } ),
					make_equal_actor( [&]( const term & l, const term & r ){ return make_equal( (*this)(l), (*this)(r) ); } ),
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
					make_propositional_letter_actor( [&]( const std::string & str ){ return make_propositional_letter( str ); } )
				);
		}
		substitution( const std::map< variable, term > & data ) : data( data ) { }
	};
	boost::optional< substitution > unify( const sentence & p, const sentence & q, const substitution & sub )
	{
		throw p;
		throw q;
		throw sub;
	}
	boost::optional< substitution > unify( const variable & var, const term & t, const substitution & sub )
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
		auto occur_check =
			[]( const variable & argvar, const term & argt )
			{
				auto inner =
					[]( const auto & self, const variable & var, const term & t )->bool
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
										[&]( const term & te ){ return self( self, var, te ); } );
						}
						throw std::invalid_argument( "unknown enum type." );
					};
				return inner( inner, argvar, argt );
			};
		if ( occur_check ) { return boost::optional< substitution >( ); }
		substitution ret( sub );
		ret.data.insert( { var, t } );
		return ret;
	}
}
#endif // SUBSTITUTION_HPP
