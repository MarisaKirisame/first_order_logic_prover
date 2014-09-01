#ifndef FIRST_ORDER_LOGIC_TERM_GENERATOR
#define FIRST_ORDER_LOGIC_TERM_GENERATOR
#include "function.hpp"
#include <set>
#include <cassert>
#include <map>
#include <vector>
#include <algorithm>
#include "atomic_sentence.hpp"
#include "complex_sentence.hpp"
namespace first_order_logic
{
	template< class deduction_tree >
	struct sentence_generator
	{
		deduction_tree * that;
		size_t arity;
		std::map< atomic_sentence, std::set< term > > & cv;
		std::set< atomic_sentence > sentence_map;
		std::map< function, std::pair< sentence_generator, sentence_generator > > functions;
		const std::set< function > & original_functions;
		sentence_generator( const sentence_generator & tg ) :
			that( tg.that ), arity( tg.arity ), cv( tg.cv ), sentence_map( tg.sentence_map ),
			original_functions( tg.original_functions ), i( this->functions.begin( ) )	{ }
		sentence_generator( deduction_tree * that, size_t arity, decltype( cv ) & cv, const std::set< function > & functions )
			: that( that), arity( arity ), cv( cv ), original_functions( functions ), i( this->functions.begin( ) ) { }
		decltype( functions.begin( ) ) i;
		std::vector< atomic_sentence > generate( decltype( functions.begin( ) ) it )
		{
			auto f = it->second.first.generate( );
			auto s = it->second.second.generate( );
			f.reserve( f.size( ) + s.size( ) );
			std::copy( s.begin( ), s.end( ), std::back_inserter( f ) );
			if ( arity == 1 ) { return { make_function( it->first.name,  f ) }; }
			else
			{
				assert( f.size( ) == arity );
				return f;
			}
		}
		sentence_generator generate_sentence_generator( size_t a ) const { return sentence_generator( that, a, cv, original_functions ); }
		std::vector< term > generate( )
		{
			if ( arity == 0 ) { return { }; }
			else
			{
				for ( auto it : cv )
				{
					if ( sentence_map.count( it.first ) == 0 )
					{
						sentence_map.insert( it.first );
						return { it.first };
					}
				}
				if ( functions.size( ) != original_functions.size( ) )
				{
					std::transform(
								original_functions.begin( ),
								original_functions.end( ),
								std::inserter( functions, functions.end( ) ),
								[this]( const function & f )
					{
						assert( f.arity != 0 );
						return std::make_pair( f, std::make_pair( generate_sentence_generator( f.arity - 1 ), generate_sentence_generator( 1 ) ) );
					} );
				}
				if ( i == functions.end( ) ) { i = functions.begin( ); }
				if ( i == functions.end( ) ) { return { that->new_variable( ) }; }
				auto ret = generate( i );
				if ( i != functions.end( ) ) { ++i; }
				assert( ret.size( ) == arity );
				assert( ! ret[0]->is_quantifier( ) );
				return ret;
			}
		}
	};
}
#endif //FIRST_ORDER_LOGIC_TERM_GENERATOR
