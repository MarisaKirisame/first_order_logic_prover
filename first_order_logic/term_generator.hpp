#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_TERM_GENERATOR
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_TERM_GENERATOR
#include "function.hpp"
#include <set>
#include <cassert>
namespace theorem_prover
{
	namespace first_order_logic
	{
		template< class term >
		struct term_generator
		{
			size_t arity;
			std::map
			<
				std::shared_ptr< term >,
				std::set< std::shared_ptr< term >, typename term::term_sort >,
				typename term::term_sort
			> & cv;
			std::set
			<
				std::shared_ptr< term >,
				typename term::term_sort
			> term_map;
			std::map< function, std::pair< term_generator, term_generator > > functions;
			const std::set< function > & original_functions;
			term_generator( const term_generator & tg ) :
				arity( tg.arity ), cv( tg.cv ), term_map( tg.term_map ), original_functions( tg.original_functions ), i( this->functions.begin( ) )	{ }
			term_generator( size_t arity, decltype( cv ) & cv, const std::set< function > & functions )
				: arity( arity ), cv( cv ), original_functions( functions ), i( this->functions.begin( ) ) { }

			decltype( functions.begin( ) ) i;
			std::vector< std::shared_ptr< term > > generate( decltype( functions.begin( ) ) it )
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

			term_generator generate_term_generator( size_t a ) { return term_generator( a, cv, original_functions ); }

			std::vector< std::shared_ptr< term > > generate( )
			{
				if ( arity == 0 ) { return { }; }
				else
				{
					for ( auto it : cv )
					{
						assert( ! it.first->is_quantifier( ) );
						if ( term_map.count( it.first ) == 0 )
						{
							term_map.insert( it.first );
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
							return std::make_pair( f, std::make_pair( generate_term_generator( f.arity - 1 ), generate_term_generator( 1 ) ) );
						} );
					}
					if ( i == functions.end( ) ) { i = functions.begin( ); }
					assert( i != functions.end( ) );
					auto ret = generate( i );
					if ( i != functions.end( ) ) { ++i; }
					assert( ret.size( ) == arity );
					assert( ! ret[0]->is_quantifier( ) );
					return ret;
				}
			}
		};
	}
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_TERM_GENERATOR
