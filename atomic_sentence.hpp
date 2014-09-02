#ifndef FIRST_ORDER_LOGIC_ATOMIC_SENTENCE
#define FIRST_ORDER_LOGIC_ATOMIC_SENTENCE
#include "function.hpp"
#include "predicate.hpp"
#include "proof_tree.hpp"
#include <boost/optional.hpp>
#include <set>
#include <boost/function_output_iterator.hpp>
#include "term.hpp"
namespace first_order_logic
{
	struct atomic_sentence
	{
		enum class type
		{
			equal, predicate, propositional_letter
		};

		struct internal
		{
			type as_type;
			std::string name;
			size_t arity( ) const { return arguments.size( ); }
			std::vector< term > arguments;
			internal( type as_type, const std::string & name, const std::vector<term> & arguments ) :
				as_type( as_type ), name( name ), arguments( arguments ) { }
		};
		std::shared_ptr< internal > data;
		internal * operator ->( ) const { return data.get( ); }
		internal & operator * ( ) const { return * data; }
		bool operator == ( const atomic_sentence & comp ) const { return ! ( * this < comp ) && ! ( comp < * this ); }
		bool operator < ( const atomic_sentence & comp ) const
		{ return std::tie( (*this)->as_type, (*this)->name, (*this)->arguments ) < std::tie( comp->as_type, (*this)->name, comp->arguments ); }
		atomic_sentence( ) { }
		atomic_sentence( type t, const std::string & name, const std::vector< term > & il ) : data( new internal( t, name, il ) ) { }
		atomic_sentence( const std::shared_ptr< internal > & ptr ) : data( ptr ) { }
		atomic_sentence( const term & t ) { throw t; }
		explicit operator std::string( ) const
		{
			switch ( (*this)->as_type )
			{
			case type::equal:
				return "(" + static_cast< std::string >( (*this)->arguments[0] ) + "=" + static_cast< std::string >( (*this)->arguments[1] ) + ")";
			case type::predicate:
			{
				std::string stack;
				for ( const auto & i : (*this)->arguments )
				{
					if( ! stack.empty( ) ) { stack += ", "; };
					stack += static_cast< std::string >( i );
				}
				return (*this)->name + "(" + stack + ")";
			}
			case type::propositional_letter:
				return static_cast< std::string >( (*this)->arguments[0] );
			}
		}
		size_t length( ) const
		{
			return std::accumulate( (*this)->arguments.begin( ),
									(*this)->arguments.end( ),
									1,
									[&]( size_t s, const term & t ){ return s + t.length( ); } );
		}
		std::set< function > functions( )
		{
			std::set< function > ret;
			std::for_each(
						(*this)->arguments.begin( ),
						(*this)->arguments.end( ),
						[&]( const term & t )
						{
							auto func = t.functions( );
							std::for_each( func.begin( ), func.end( ), [&]( const function & t ){ ret.insert( t ); } );
						} );
				return ret;
		}
	};
}
#endif //FIRST_ORDER_LOGIC_ATOMIC_SENTENCE
