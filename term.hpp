#ifndef TERM_HPP
#define TERM_HPP
#include <cassert>
#include "boost/function_output_iterator.hpp"
#include "function.hpp"
#include <vector>
#include <memory>
#include <algorithm>
#include <set>
#include "variable.hpp"
#include "constant.hpp"
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
		term( type term_type, const std::string & name, const std::vector< term > & arguments ) :
			data( new internal( term_type, name, arguments ) ) { }
		term( const std::shared_ptr< internal > & data ) : data( data ) { }
		std::set< constant > constants( ) const
		{
			switch ( (*this)->term_type )
			{
			case type::variable:
				return { };
			case type::constant:
				return { term( data ) };
			case type::function:
				{
					std::set< constant > ret;
					std::transform( (*this)->arguments.begin( ),
									(*this)->arguments.end( ),
									boost::make_function_output_iterator( [&]( const std::set< constant > & s ){ ret.insert( s.begin( ), s.end( ) ); } ),
									[&]( const term & t ){ return t.constants( ); } );
					return ret;
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
		std::set< variable > free_variables( ) const
		{
			switch ( (*this)->term_type )
			{
			case type::variable:
				return { term( data ) };
			case type::constant:
				return { };
			case type::function:
				{
					std::set< variable > ret;
					std::transform( (*this)->arguments.begin( ),
									(*this)->arguments.end( ),
									boost::make_function_output_iterator(
										[&]( const std::set< variable > & s ){ ret.insert( s.begin( ), s.end( ) ); } ),
									[&]( const term & t ){ return t.free_variables( ); } );
					return ret;
				}
			}
			throw std::invalid_argument( "unknown enum type" );
		}
		std::set< function > functions( ) const
		{
			std::set< function > ret;
			if ( (*this)->term_type == type::function ) { ret.insert( function( (*this)->name, (*this)->arguments.size( ) ) ); }
			std::for_each(
						(*this)->arguments.begin( ),
						(*this)->arguments.end( ),
						[&]( const term & t )
						{
							auto tem = t.functions( );
							ret.insert( tem.begin( ), tem.end( ) );
						} );
			return ret;
		}
		const internal * operator -> ( ) const { return data.get( ); }
		explicit operator std::string( ) const
		{
			if ( ! (*this)->cache.empty( ) ) { return (*this)->cache; }
			assert( data );
			std::string stack;
			auto it = (*this)->arguments.begin( );
			if ( it != (*this)->arguments.end( ) ) { goto http; }
			while ( it != (*this)->arguments.end( ) )
			{
				stack += ", ";
				http://marisa.moe
				assert( it->data );
				stack += static_cast< std::string >( * it );
				++it;
			}
			(*this)->cache = (*this)->name + ( stack.empty( ) ? "" : "(" + stack + ")" );
			return (*this)->cache;
		}
		bool operator < ( const term & comp ) const { return static_cast< std::string >( * this ) < static_cast< std::string >( comp ); }
		term( ) { }
		term( const variable & var ) : data( new internal( type::variable, var.name, { } ) ) { }
		term( const constant & var ) : data( new internal( type::variable, var.name, { } ) ) { }
	};
}
#endif // TERM_HPP
