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
#include <boost/optional.hpp>
namespace first_order_logic
{
	struct gentzen_system
	{
		struct sequence
		{
			proof_tree pt;
			term new_variable( )
			{
				term ret = make_variable( std::to_string( unused++ ) );
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
			term_generator< sequence > tg;
			std::vector< std::tuple< sequence, proof_tree, boost::optional< bool > > > branch;
			sequence * parent = nullptr;
			bool have_branch = false;
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
			boost::optional< bool > expand( proof_tree & leaf )
			{
				if ( have_branch )
				{
					auto try_join =
						[&]( )->boost::optional< bool >
						{
							if ( std::all_of(
									branch.begin( ),
									branch.end( ),
									[&]( const auto & t ) { return std::get< 2 >( t ) == true; } ) )
									{
										std::for_each( branch.begin( ), branch.end( ), [&]( const auto & t ){ leaf.join( std::get< 1 >( t ) ); } );
										return true;
									}
									auto it = std::find_if( branch.begin( ), branch.end( ), [&]( const auto & t ){ return std::get< 2 >( t ) == false; } );
									if ( it != branch.end( ) )
									{
										leaf.join( std::get< 1 >( * it ) );
										return false;
									}
							return boost::optional< bool >( );
						};
					for ( std::tuple< sequence, proof_tree, boost::optional< bool > > & p : branch )
					{
						if ( ! std::get< 2 >( p ) )
						{
							std::get< 2 >( p ) = std::get< 0 >( p ).expand( std::get< 1 >( p ) );
							auto ret = try_join( );
							if ( ret ) { return ret; }
						}
					}
					return try_join( );
				}
				if ( sequent.empty( ) )
				{
					sequent.swap( temp_sequent );
					auto f = tg.generate( );
					assert( f.size( ) == 1 );
					term_map.insert( std::make_pair( f[0], std::set< sentence >( ) ) );
				}
				if ( sequent.empty( ) ) { return false; }
				while ( ( ! sequent.empty( ) ) && branch.empty( ) )
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
										assert( branch.empty( ) );
										sequence ldt( * this );
										sequence rdt( * this );
										try
										{
											ldt.try_insert( ldt.sequent, l, false );
											branch.push_back( std::make_tuple( ldt, proof_tree( ), boost::optional< bool >( ) ) );
										}
										catch ( contradiction & con ) { pt.join( con.pt ); }
										try
										{
											rdt.try_insert( rdt.sequent, r, false );
											branch.push_back( std::make_tuple( rdt, proof_tree( ), boost::optional< bool >( ) ) );
										}
										catch ( contradiction & con ) { pt.join( con.pt ); }
										have_branch = true;
									}
								} ),
							make_or_actor(
								[&]( const sentence & l, const sentence & r )
								{
									if ( t.second )
									{
										assert( branch.empty( ) );
										sequence ldt( * this );
										sequence rdt( * this );
										try
										{
											ldt.try_insert( ldt.sequent, l, true );
											branch.push_back( std::make_tuple( ldt, proof_tree( ), boost::optional< bool >( ) ) );
										}
										catch ( contradiction & con ) { pt.join( con.pt ); }
										try
										{
											rdt.try_insert( rdt.sequent, r, true );
											branch.push_back( std::make_tuple( rdt, proof_tree( ), boost::optional< bool >( ) ) );
										}
										catch ( contradiction & con ) { pt.join( con.pt ); }
										have_branch = true;
									}
									else
									{
										try_insert( sequent, l, false );
										try_insert( sequent, r, false );
									}
								} ),
							make_not_actor( [&]( const sentence & sen ) { try_insert( sequent, sen, ! t.second ); } )
						);
					}
					catch ( contradiction & con )
					{
						leaf.join( con.pt );
						return true;
					}
					leaf = leaf.join( proof_tree( static_cast< std::string >( * this ) ) );
				}
				return boost::optional< bool >( );
			}
			bool is_valid( )
			{
				pt = proof_tree( static_cast< std::string >( * this ) );
				proof_tree leaf = pt;
				while ( true )
				{
					auto ret = expand( leaf );
					if ( ret ) { return * ret; }
				}
				return false;
			}
			sequence( const sequence & t ) :
				sequent( t.sequent ),
				temp_sequent( t.temp_sequent ),
				cv_map( t.cv_map ),
				term_map( t.term_map ),
				expanded( t.expanded ),
				unused( t.unused ),
				functions( t.functions ),
				predicates( t.predicates ),
				tg( this, 1, cv_map, functions ) { }
			sequence( const sentence & t ) :
				sequent( { { t, false } } ), functions( t.functions( ) ), predicates( t.predicates( ) ), tg( this, 1, cv_map, functions )
			{
				const auto cv = t.cv( );
				std::transform(
							cv.begin( ),
							cv.end( ),
							std::inserter( cv_map, cv_map.begin( ) ),
							[]( const term & s ){ return std::make_pair( s, std::set< sentence >( ) ); } );
				term_map = cv_map;
				if ( cv_map.empty( ) ) { new_variable( ); }
				if ( t.have_equal( ) ) { add_equal_generator( ); }
			}
		};
		static std::pair< proof_tree, bool > is_valid( sentence & te )
		{
			sequence t( te );
			bool res = t.is_valid( );
			return std::make_pair( t.pt, res );
		}
	};
}
#endif //FIRST_ORDER_LOGIC_DEDUCTION_TREE
