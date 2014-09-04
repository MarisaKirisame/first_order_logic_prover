#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_DEDUCTION_TREE
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_DEDUCTION_TREE
#include "predicate.hpp"
#include "memory"
#include "utility"
#include "term_generator.hpp"
#include "boost/range.hpp"
#include "boost/range/join.hpp"
#include "boost/iterator/counting_iterator.hpp"
#include "function.hpp"
#include "predicate.hpp"
#include "proof_tree.hpp"
#include "sentence.hpp"
#include "first_order_logic.hpp"
#include "substitution.hpp"
namespace first_order_logic
{
	struct gentzen_system
	{
		proof_tree pt;
		variable new_variable( )
		{
			variable ret = make_variable( std::to_string( unused++ ) );
			cv_map.insert( std::make_pair( ret, std::set< sentence >( ) ) );
			return ret;
		}
		std::map< sentence, bool > sequent;
		std::map< sentence, bool > temp_sequent;
		std::map
		<
			term,
			std::set< sentence >
		> cv_map, term_map;
		std::map< sentence, bool > expanded;
		size_t unused = 0;
		std::set< function > functions;
		std::set< predicate > predicates;
		term_generator< gentzen_system > tg;
		bool is_valid( proof_tree & pt, sentence t, bool b )
		{
			gentzen_system dt( * this );
			try { dt.try_insert( dt.sequent, t, b ); }
			catch ( contradiction & con )
			{
				join( pt, con.pt );
				return true;
			}
			auto res = dt.is_valid( );
			join( pt, dt.pt );
			return res;
		}
		struct contradiction { proof_tree pt; };
		void try_insert(
				std::map< sentence, bool > & m,
				const sentence & t,
				bool b )
		{
			if ( m.insert( std::make_pair( t, b ) ).first->second != b )
			{
				contradiction con;
				auto res = pair_str( );
				std::string & str = b ? res.first : res.second;
				if ( ! str.empty( ) ) { str += ","; }
				str += static_cast< std::string >( t );
				con.pt = ( res.first + "-->" + res.second );
				throw con;
			}
		}
		proof_tree join( proof_tree & parent, proof_tree child )
		{
			child->parent = parent.data.get( );
			if ( child->str != parent->str )
			{
				parent->child.push_back( child );
				return child;
			}
			return parent;
		}
		void add_equal_generator( const function & f )
		{
			assert( f.arity >= 1 );
			if ( f.arity == 1 )
			{
				try_insert
				(
					sequent,
					make_all
					(
						"s",
						make_all
						(
							"t",
							make_imply
							(
								make_equal( make_variable( "s" ), make_variable( "t" ) ),
								make_equal
								(
									make_function( f.name, { make_variable( "s" ) } ),
									make_function( f.name, { make_variable( "t" ) } )
								)
							)
						)
					),
					true
				);
			}
			else
			{
				std::vector< term > args, argt;
				args.reserve( f.arity );
				argt.reserve( f.arity );
				std::for_each(
					boost::counting_iterator< size_t >( 0 ),
					boost::counting_iterator< size_t >( f.arity ),
					[&]( size_t i )
					{
						args.push_back( make_variable( "s" + std::to_string( i ) ) );
						argt.push_back( make_variable( "t" + std::to_string( i ) ) );
					} );
				sentence and_stack = make_and( make_equal( args[0], argt[0] ), make_equal( args[1], argt[1] ) );
				for ( size_t i = 2; i < f.arity; ++i ) { and_stack = make_and( and_stack, make_equal( args[i], argt[i] ) ); }
				auto add = make_imply( and_stack, make_equal( make_function( f.name, args ), make_function( f.name, argt ) ) );
				for ( size_t i = 0; i < f.arity; ++i ) { add = make_all( args[i]->name, make_all( argt[i]->name, add ) ); }
				try_insert( sequent, add, true );
			}
		}
		void add_equal_generator( const predicate & f )
		{
			assert( f.arity >= 1 );
			if ( f.arity == 1 )
			{
				try_insert
				(
					sequent,
					make_all
					(
						"s",
						make_all
						(
							"t",
							make_imply
							(
								make_and
								(
									make_equal( make_variable( "s" ), make_variable( "t" ) ),
									make_predicate( f.name, { make_variable( "s" ) } )
								),
								make_predicate( f.name, { make_variable( "t" ) } )
							)
						)
					),
					true
				);
			}
			else
			{
				std::vector< term > args, argt;
				args.reserve( f.arity );
				argt.reserve( f.arity );
				std::for_each(
					boost::counting_iterator< size_t >( 0 ),
					boost::counting_iterator< size_t >( f.arity ),
					[&]( size_t i )
					{
						args.push_back( make_variable( "s" + std::to_string( i ) ) );
						argt.push_back( make_variable( "t" + std::to_string( i ) ) );
					} );
				sentence and_stack = make_and( make_equal( args[0], argt[0] ), make_equal( args[1], argt[1] ) );
				try_insert( sequent, make_imply( make_and( and_stack, make_predicate( f.name, args ) ), make_predicate( f.name, argt ) ), true );
			}
		}
		void add_equal_generator( )
		{
			try_insert( sequent, make_all( "t", make_equal( make_variable( "t" ), make_variable( "t" ) ) ), true );
			try_insert( sequent,
						make_all
						(
							"x",
							make_all
							(
								"y",
								make_imply
								(
									make_equal( make_variable( "x" ), make_variable( "y" ) ),
									make_equal( make_variable( "y" ), make_variable( "x" ) )
								)
							)
						), true );
			try_insert( sequent,
						make_all
						(
							"s1",
							make_all
							(
								"t1",
								make_all
								(
									"s2",
									make_all
									(
										"t2",
										make_imply
										(
											make_and
											(
												make_and
												(
													make_equal( make_variable( "s1" ), make_variable( "t1" ) ),
													make_equal( make_variable( "s2" ), make_variable( "t2" ) )
												),
												make_equal( make_variable( "s1" ), make_variable( "s2" ) )
											),
											make_equal( make_variable( "t1" ), make_variable( "t2" ) )
										)
									)
								)
							)
						),
						true );
			std::for_each( functions.begin( ), functions.end( ), [this]( const function & f ){ add_equal_generator( f ); } );
			std::for_each( predicates.begin( ), predicates.end( ), [this]( const predicate & f ){ add_equal_generator( f ); } );
		}
		explicit operator std::string( ) const
		{
			auto res = pair_str( );
			return res.first + "-->" + res.second;
		}
		std::pair< std::string, std::string > pair_str( ) const
		{
			std::string postive, negative;
			auto function = [&]( const std::pair< sentence, bool > & val )
			{
				std::string & str = val.second ? postive : negative;
				if ( ! str.empty( ) ) { str += ","; }
				str += static_cast< std::string >( val.first );
			};
			std::for_each( temp_sequent.begin( ), temp_sequent.end( ), function );
			std::for_each( sequent.begin( ), sequent.end( ), function );
			std::for_each( expanded.begin( ), expanded.end( ), function );
			return std::make_pair( postive, negative );
		}
		bool is_valid( )
		{
			pt = proof_tree( static_cast< std::string >( * this ) );
			proof_tree leaf = pt;
			try
			{
				while ( ! sequent.empty( ) || ! temp_sequent.empty( ) )
				{
					if ( sequent.empty( ) )
					{
						sequent.swap( temp_sequent );
						auto f = tg.generate( );
						assert( f.size( ) == 1 );
						term_map.insert( std::make_pair( f[0], std::set< sentence >( ) ) );
					}
					while ( ! sequent.empty( ) )
					{
						std::pair< sentence, bool > t = * sequent.begin( );
						sequent.erase( sequent.begin( ) );
						try
						{
							t.first.type_restore_full
							(
								make_all_actor(
									[&]( const variable & var, const sentence & sen )
									{
										if ( t.second )
										{
											std::for_each
											(
												term_map.begin( ),
												term_map.end( ),
												[&,this]( auto & s )
												{
													if ( s.second.count( t.first ) == 0 )
													{
														s.second.insert( t.first );
														this->try_insert
														(
															sequent,
															substitution( { { var, s.first } } )( sen ),
															true
														);
													}
												}
											);
											try_insert( temp_sequent, t.first, true );
										}
										else { try_insert( sequent, substitution( { { var, term( new_variable( ) ) } } )( sen ), false ); }
									} ),
								make_some_actor(
									[&]( const variable & var, const sentence & sen )
									{
										if ( t.second ) { try_insert( sequent, substitution( { { var, term( new_variable( ) ) } } )( sen ), true ); }
										else
										{
											std::for_each
											(
												term_map.begin( ),
												term_map.end( ),
												[&,this]( auto & s )
												{
													if ( s.second.count( t.first ) == 0 )
													{
														s.second.insert( t.first );
														this->try_insert
														(
															sequent,
															substitution( { { var, s.first } } )( sen ),
															false
														);
													}
												}
											);
											try_insert( temp_sequent, t.first, false );
										}
									} ),
								make_equal_actor(
									[&]( const term & l, const term & r ) { try_insert( expanded, make_equal( l, r ), t.second ); } ),
								make_predicate_actor(
									[&]( const std::string & str, const std::vector< term > & vec )
									{ try_insert( expanded, make_predicate( str, vec ), t.second ); } ),
								make_propositional_letter_actor(
									[&]( const std::string & str )
									{ try_insert( expanded, make_propositional_letter( str ), t.second ); } ),
								make_and_actor(
									[&]( const sentence & l, const sentence & r )
									{
										if ( t.second )
										{
											try_insert( sequent, l, true );
											try_insert( sequent, r, true );
										}
										else
										{
											if ( ! is_valid( leaf, l, false ) ) { throw false; }
											try_insert( sequent, r, false );
										}
									} ),
								make_or_actor(
									[&]( const sentence & l, const sentence & r )
									{
										if ( t.second )
										{
											if ( ! is_valid( leaf, l, true ) ) { throw false; }
											try_insert( sequent, r, true );
										}
										else
										{
											try_insert( sequent, l, false );
											try_insert( sequent, r, false );
										}
									} ),
								make_not_actor( [&]( const sentence & sen ) { try_insert( sequent, sen, ! t.second ); } )
							);
							leaf = join( leaf, proof_tree( static_cast< std::string >( * this ) ) );
						}
						catch( bool ret ) { return ret; }
					}
				}
				return false;
			}
			catch ( contradiction & con )
			{
				join( leaf, con.pt );
				return true;
			}
		}
		gentzen_system( const gentzen_system & t ) :
			sequent( t.sequent ),
			temp_sequent( t.temp_sequent ),
			cv_map( t.cv_map ),
			term_map( t.term_map ),
			expanded( t.expanded ),
			unused( t.unused ),
			functions( t.functions ),
			predicates( t.predicates ),
			tg( this, 1, cv_map, functions ) { }
		gentzen_system( const sentence & t ) :
			sequent( { { t, false } } ), functions( t.functions( ) ), predicates( t.predicates( ) ), tg( this, 1, cv_map, functions )
		{
			const auto fv = t.free_variables( );
			const auto con = t.constants( );
			std::transform(
						fv.begin( ),
						fv.end( ),
						std::inserter( cv_map, cv_map.begin( ) ),
						[]( const term & s ){ return std::make_pair( s, std::set< sentence >( ) ); } );
			std::transform(
						con.begin( ),
						con.end( ),
						std::inserter( cv_map, cv_map.begin( ) ),
						[]( const term & s ){ return std::make_pair( s, std::set< sentence >( ) ); } );
			term_map = cv_map;
			if ( cv_map.empty( ) ) { new_variable( ); }
			if ( t.have_equal( ) ) { add_equal_generator( ); }
		}
		static std::pair< proof_tree, bool > is_valid( sentence & te )
		{
			gentzen_system t( te );
			bool res = t.is_valid( );
			return std::make_pair( t.pt, res );
		}
	};
}
#endif //FIRST_ORDER_LOGIC_DEDUCTION_TREE
