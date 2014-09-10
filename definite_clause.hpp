#ifndef DEFINITE_CLAUSE_HPP
#define DEFINITE_CLAUSE_HPP
#include "term.hpp"
#include <vector>
#include "substitution.hpp"
#include "sentence.hpp"
namespace first_order_logic
{
	struct definite_clause
	{
		std::vector< sentence > premise;
		sentence conclusion;
	};
	struct knowledge_base
	{
		std::vector< definite_clause > kb;
		std::vector< sentence > known_facts;
		template< typename ITER >
		ITER matching_facts( const sentence & match, const substitution & sub, ITER result )
		{
			for ( const sentence & sen : known_facts )
			{
				auto res = unify( match, sen, sub );
				if ( res ) { * result = { sen, * res }; }
			}
			return result;
		}
		boost::optional< substitution > forward_chaining( const sentence & sen )
		{
			bool have_new_inference = true;
			while ( have_new_inference )
			{
				have_new_inference = false;
				for ( size_t i = 0; i < kb.size( ); ++i )
				{
					const definite_clause & dc = kb[i];
					substitution s;
					std::vector< sentence > gp;
					auto generate =
							[&]( const auto & self, const substitution & sub )
							{
								if ( gp.size( ) == dc.premise.size( ) )
								{
									known_facts.push_back( sub( dc.conclusion ) );
									have_new_inference = true;
								}
								else
								{
									matching_facts(
										dc.premise[ gp.size( ) ],
										sub,
										boost::make_function_output_iterator(
											[&]( const std::pair< sentence, substitution > & p )
											{
												if ( unify( known_facts.back( ), sen ) )
												{
													gp.push_back( p.first );
													self( self, p.second );
													gp.pop_back( );
												}
											} ) );
								}
							};
					generate( generate, gp, s );
					auto ret = unify( known_facts.back( ), sen );
					if ( ret ) { return ret; }
				}
			}
			return boost::optional< substitution >( );
		}
	};
}
#endif // DEFINITE_CLAUSE_HPP
