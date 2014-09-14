#ifndef KNOWLEDGE_BASE_HPP
#define KNOWLEDGE_BASE_HPP
#include "definite_clause.hpp"
namespace first_order_logic
{
	struct knowledge_base
	{
		std::vector< definite_clause > kb;
		std::vector< sentence > known_facts;
		template< typename ITER >
        ITER matching_facts( const sentence & match, const substitution & sub, ITER result ) const
		{
			for ( auto i = known_facts.begin( ); i != known_facts.end( ); ++i )
			{
				const auto & sen = * i;
				assert( static_cast< bool >( sen.data ) );
				auto res = unify( match, sen, sub );
				if ( res ) { * result = std::make_pair( sen, * res ); }
			}
			return result;
		}
		boost::optional< substitution > forward_chaining( const sentence & sen )
		{
			for ( const sentence & se : known_facts )
			{
				auto ret = unify( se, sen );
				if ( ret ) { return ret; }
			}
			bool have_new_inference = true;
			std::set< std::string > variable_name;
			auto extract =
					[&]( const sentence & s )
					{
						std::set< term > v = s.cv( );
						std::transform(
									v.begin( ),
									v.end( ),
									std::inserter( variable_name, variable_name.begin( ) ),
									[]( const term & t ){ return t->name; } );
					};
			for ( const definite_clause & dc : kb )
			{
				std::for_each( dc.premise.begin( ), dc.premise.end( ), extract );
				extract( dc.conclusion );
			}
			while ( have_new_inference )
			{
				have_new_inference = false;
				for ( size_t i = 0; i < kb.size( ); ++i )
				{
					const definite_clause & dc = kb[i];
					assert( ! dc.premise.empty( ) );
					substitution rename =
							rename_variable(
								dc.premise.begin( ),
								dc.premise.end( ),
								[&]( const std::string & v ){ return variable_name.count( v ) == 0; },
								[]( const std::string & n ){ return n + "_"; } );
					substitution s;
					std::vector< sentence > gp;
					std::vector< sentence > new_known_facts;
					auto generate =
							[&,this]( const auto & self, const substitution & sub )->void
							{
								if ( gp.size( ) == dc.premise.size( ) ) { new_known_facts.push_back( sub( rename( dc.conclusion ) ) ); }
								else
								{
									this->matching_facts(
										rename( dc.premise[ gp.size( ) ] ),
										sub,
										boost::make_function_output_iterator(
											[&]( const std::pair< sentence, substitution > & p )
											{
												if ( ! unify( known_facts.back( ), sen ) )
												{
													gp.push_back( p.first );
													self( self, p.second );
													gp.pop_back( );
												}
											} ) );
								}
							};
					generate( generate, s );
					for ( const sentence & sen : new_known_facts )
					{
						if ( std::none_of(
								known_facts.begin( ),
								known_facts.end( ),
								[&]( const sentence & s ){ return unify( sen, s ); } ) )
						{
							known_facts.push_back( sen );
							have_new_inference = true;
						}
					}
					std::copy( new_known_facts.begin( ), new_known_facts.end( ), std::back_inserter( known_facts ) );
					auto ret = unify( known_facts.back( ), sen );
					if ( ret ) { return ret; }
				}
			}
			return boost::optional< substitution >( );
		}
	};
}
#endif // KNOWLEDGE_BASE_HPP
