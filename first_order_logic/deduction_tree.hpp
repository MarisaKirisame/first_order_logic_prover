#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_DEDUCTION_TREE
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_DEDUCTION_TREE
#include "term_generator.hpp"
#include "first_order_logic.hpp"
#include "boost/range.hpp"
#include "boost/range/join.hpp"
namespace theorem_prover
{
	namespace first_order_logic
	{
		struct term;
		std::shared_ptr< term > make_variable( const std::string & s );
		template< class term >
		struct deduction_tree
		{
			std::shared_ptr< term > new_variable( )
			{
				auto ret = make_variable( std::to_string( unused++ ) );
				cv_map.insert( std::make_pair( ret,  std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >( ) ) );
				return ret;
			}
			std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > sequent;
			std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > temp_sequent;
			std::map
			<
				std::shared_ptr< term >,
				std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >,
				value_less< std::shared_ptr< term > >
			> cv_map, term_map;
			std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > expanded;
			size_t unused = 0;
			std::set< function > functions;
			term_generator< term > tg;
			bool is_valid( std::shared_ptr< term > t, bool b )
			{
				deduction_tree dt( * this );
				try { dt.try_insert( dt.sequent, t, b ); }
				catch ( contradiction & ) { return true; }
				return dt.is_valid( );
			}

			struct contradiction { };
			void try_insert(
					std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > & m,
					const std::shared_ptr< term > & t,
					bool b )			{
				if ( m.insert( std::make_pair( t, b ) ).first->second != b )
				{
					contradiction con;
					throw con;
				}
			}

			bool is_valid( )
			{
				try
				{
					while ( ! sequent.empty( ) || ! temp_sequent.empty( ) )
					{
						if ( sequent.empty( ) )
						{
							sequent.swap( temp_sequent );
							auto f = tg.generate( );
							assert( f.size( ) == 1 );
							assert( ! f[0]->is_quantifier( ) );
							term_map.insert(
										std::make_pair(
											f[0],
											std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >( ) ) );
						}
						while ( ! sequent.empty( ) )
						{
							auto t = * sequent.begin( );
							sequent.erase( sequent.begin( ) );
							if ( t.first->name == "variable" ) { try_insert( expanded, t.first, t.second ); }
							else if ( t.first->name == "constant" ) { throw std::runtime_error( "invalid sequent." ); }
							else if ( t.first->is_quantifier( ) )
							{
								assert( t.first->arguments.size( ) == 2 );
								if ( t.first->name == "all" )
								{
									if ( t.second )
									{
										std::for_each( term_map.begin( ), term_map.end( ),
																	 [&](
																	 std::pair
																	 <
																		const std::shared_ptr< term >,
																		std::set
																		<
																			std::shared_ptr< term >,
																			value_less< std::shared_ptr< term > >
																		>
																	 > & s )
										{
											if ( s.second.count( t.first ) == 0 )
											{
												s.second.insert( t.first );
												try_insert( sequent, t.first->rebound( t.first->arguments[0], s.first ), true );
											}
										} );
										try_insert( temp_sequent, t.first, true );
									}
									else { try_insert( sequent, t.first->rebound( t.first->arguments[0], new_variable( ) ), false ); }
								}
								else
								{
									assert( t.first->name == "some" );
									if ( t.second ) { try_insert( sequent, t.first->rebound( t.first->arguments[0], new_variable( ) ), true ); }
									else
									{
										std::for_each( term_map.begin( ), term_map.end( ),
																	 [&](
																	 std::pair
																	 <
																		const std::shared_ptr< term >,
																		std::set
																		<
																			std::shared_ptr< term >,
																			value_less< std::shared_ptr< term > >
																		>
																	 > & s )
										{
											if ( s.second.count( t.first ) == 0 )
											{
												s.second.insert( t.first );
												try_insert( sequent, t.first->rebound( t.first->arguments[0], s.first ), false );
											}
										} );
										try_insert( temp_sequent, t.first, false );
									}
								}
							}
							else
							{
								if ( t.first->name == "not" )
								{
									assert( t.first->arguments.size( ) == 1 );
									try_insert( sequent, t.first->arguments[0], ! t.second );
								}
								else if ( t.first->name == "and" )
								{
									assert( t.first->arguments.size( ) == 2 );
									if ( t.second )
									{
										try_insert( sequent, t.first->arguments[0], true );
										try_insert( sequent, t.first->arguments[1], true );
									}
									else
									{
										if ( ! is_valid( t.first->arguments[0], false ) ) { return false; }
										try_insert( sequent, t.first->arguments[1], false );
									}
								}
								else if ( t.first->name == "or" )
								{
									assert( t.first->arguments.size( ) == 2 );
									if ( t.second )
									{
										if ( ! is_valid( t.first->arguments[0], true ) ) { return false; }
										try_insert( sequent, t.first->arguments[1], true );
									}
									else
									{
										try_insert( sequent, t.first->arguments[0], false );
										try_insert( sequent, t.first->arguments[1], false );
									}
								}
								else { try_insert( expanded, t.first, t.second ); }
							}
						}
					}
					return false;
				}
				catch ( contradiction & ) { return true; }
			}

			deduction_tree( const deduction_tree & t ) :
				sequent( t.sequent ),
				temp_sequent( t.temp_sequent ),
				cv_map( t.cv_map ),
				term_map( t.term_map ),
				expanded( t.expanded ),
				unused( t.unused ),
				functions( t.functions ),
				tg( 1, cv_map, functions ) { }
			deduction_tree( const std::shared_ptr< term > & t ) : sequent( { { t, false } } ), functions( t->functions( ) ), tg( 1, cv_map, functions )
			{
				const auto fv = t->free_variables( );
				const auto con = t->constants( );
				auto r = boost::range::join( boost::make_iterator_range( fv.begin( ), fv.end( ) ), boost::make_iterator_range( con.begin( ), con.end( ) ) );
				std::transform( r.begin( ), r.end( ), std::inserter( cv_map, cv_map.begin( ) ), [ ]( const std::shared_ptr< term > & s )
				{ return std::make_pair( s, std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >( ) ); } );
				term_map = cv_map;
				if ( cv_map.empty( ) ) { new_variable( ); }
			}
		};
	}
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_DEDUCTION_TREE
