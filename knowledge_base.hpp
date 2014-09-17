#ifndef KNOWLEDGE_BASE_HPP
#define KNOWLEDGE_BASE_HPP
#include <list>
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
		std::set< std::string > variable_name( )
		{
			std::set< std::string > ret;
			auto extract =
					[&]( const sentence & s )
					{
						std::set< term > v = s.cv( );
						std::transform(
									v.begin( ),
									v.end( ),
									std::inserter( ret, ret.begin( ) ),
									[]( const term & t ){ return t->name; } );
					};
			for ( const definite_clause & dc : kb )
			{
				std::for_each( dc.premise.begin( ), dc.premise.end( ), extract );
				extract( dc.conclusion );
			}
			return ret;
		}
		bool try_infer_forward(
				const std::vector< sentence > & premise,
				const sentence & conclusion,
				const substitution & rename,
				const sentence & query )
		{
			bool ret = false;
			std::vector< sentence > new_known_facts;
			substitution s;
			std::vector< sentence > gp;
			auto generate =
					[&,this]( const auto & self, const substitution & sub )->void
					{
						if ( gp.size( ) == premise.size( ) ) { new_known_facts.push_back( sub( rename( conclusion ) ) ); }
						else
						{
							this->matching_facts(
								rename( premise[ gp.size( ) ] ),
								sub,
								boost::make_function_output_iterator(
									[&]( const std::pair< sentence, substitution > & p )
									{
										if ( ( new_known_facts.empty( ) ) || ( ! unify( new_known_facts.back( ), query ) ) )
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
					ret = true;
				}
			}
			return ret;
		}
		boost::optional< substitution > forward_chaining( const sentence & sen )
		{
			for ( const sentence & se : known_facts )
			{
				auto ret = unify( se, sen );
				if ( ret ) { return ret; }
			}
			bool have_new_inference = true;
			std::set< std::string > var_name = variable_name( );
			while ( have_new_inference )
			{
				have_new_inference = false;
				for ( const definite_clause & dc : kb )
				{
					assert( ! dc.premise.empty( ) );
					substitution rename =
							rename_variable(
								dc.premise.begin( ),
								dc.premise.end( ),
								[&]( const std::string & v ){ return var_name.count( v ) == 0; },
								[]( const std::string & n ){ return n + "_"; } );
					have_new_inference = try_infer_forward( dc.premise, dc.conclusion, rename, sen ) || have_new_inference;
					auto ret = unify( known_facts.back( ), sen );
					if ( ret ) { return ret; }
				}
			}
			return boost::optional< substitution >( );
		}
		boost::optional< substitution > backward_chaining( const sentence & sen )
		{
			for ( const sentence & se : known_facts )
			{
				auto ret = unify( se, sen );
				if ( ret ) { return ret; }
			}
			if ( known_facts.empty( ) ) { return boost::optional< substitution >( ); }
			std::set< std::string > var_name = variable_name( );
			std::map< sentence, std::vector< std::vector< sentence > > > requiring_fact;
			bool progress = true;
			auto try_add =
					[&]( const sentence & s )
					{
						if ( requiring_fact.count( s ) == 0 )
						{
							std::vector< std::vector< sentence > > deduct_from;
							for ( const definite_clause & dc : kb )
							{
								assert( ! dc.premise.empty( ) );
								substitution rename =
										rename_variable(
											dc.premise.begin( ),
											dc.premise.end( ),
											[&]( const std::string & v ){ return var_name.count( v ) == 0; },
											[]( const std::string & n ){ return n + "_"; } );
								auto ret = unify( rename( dc.conclusion ), s );
								if ( ret )
								{
									std::vector< sentence > tem;
									for ( const sentence & se : dc.premise )
									{ tem.push_back( ( *ret )( rename( se ) ) ); }
									deduct_from.push_back( tem );
								}
							}
							requiring_fact.insert( std::make_pair( s, deduct_from ) );
							progress = true;
						}
					};
			try_add( sen );
			while ( progress )
			{
				progress = false;
				auto ret = unify( known_facts.back( ), sen );
				if ( ret ) { return ret; }
				std::vector< sentence > add;
				for ( const std::pair< sentence, std::vector< std::vector< sentence > > > & p : requiring_fact )
				{
					for ( const std::vector< sentence > & vec : p.second )
					{
						substitution rename =
								rename_variable(
									vec.begin( ),
									vec.end( ),
									[&]( const std::string & v ){ return var_name.count( v ) == 0; },
									[]( const std::string & n ){ return n + "_"; } );
						progress = try_infer_forward( vec, p.first, rename, sen ) || progress;
						auto ret = unify( known_facts.back( ), sen );
						if ( ret ) { return ret; }
						std::copy( vec.begin( ), vec.end( ), std::back_inserter( add ) );
					}
				}
				std::for_each( add.begin( ), add.end( ), try_add );
			}
			return boost::optional< substitution >( );
		}
	};
}
#endif // KNOWLEDGE_BASE_HPP
