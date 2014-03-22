#ifndef GENTZEN_SYSTEM_FIRST_ORDER_LOGIC
#define GENTZEN_SYSTEM_FIRST_ORDER_LOGIC
#include  <string>
#include "boost/variant.hpp"
#include <vector>
#include <memory>
#include <set>
#include <algorithm>
#include <map>
#include <boost/range/join.hpp>
#include <utility>
#include "value_less.hpp"
namespace gentzen_system
{
	template< typename term >
	struct set_inserter
	{
		std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > & to;
		set_inserter( std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > & s ) : to( s ) { }
		set_inserter & operator ++ ( ) { return * this; }
		set_inserter & operator ++ ( int ) { return * this; }
		set_inserter & operator = ( const std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > & s )
		{
			to.insert( s.begin( ), s.end( ) );
			return * this;
		}
		set_inserter & operator * ( ) { return * this; }
	};

	struct function
	{
		std::string name;
		size_t arity;
		function( const std::string & name, size_t arity ) : name( name ), arity( arity ) { }
		bool operator < ( const function & f ) const { return name < f.name || ( name == f.name && arity < f.arity ); }
	};
	struct term : std::enable_shared_from_this< term >
	{
		std::string name;
		size_t arity( ) const { return arguments.size( ); }
		bool is_quantifiers( ) const { return name == "some" || name == "all"; }
		std::vector< std::shared_ptr< term > > arguments;
		std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > constants( )
		{
			if ( name == "variable" )
			{
				assert( arity( ) == 1 );
				return { };
			}
			else if ( name == "constant" ) { return { shared_from_this( ) }; }
			else if ( is_quantifiers( ) )
			{
				assert( arity( ) == 2 );
				return arguments[1]->constants( );
			}
			else
			{
				std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > ret;
				std::transform( arguments.begin( ), arguments.end( ), set_inserter< term >( ret ),
												[&]( const std::shared_ptr< term > & t ){ return t->constants( ); } );
				return ret;
			}
		}

		term( const std::string & s, std::initializer_list< std::shared_ptr< term > > il ) : name( s ), arguments( il ) { }
		term( const std::string & s, const std::vector< std::shared_ptr< term > > & il ) : name( s ), arguments( il ) { }
		std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > free_variables( )
		{
			if ( name == "variable" ) { return { shared_from_this( ) }; }
			else if ( name == "constant" ) { return { }; }
			else if ( is_quantifiers( ) )
			{
				assert( arity( ) == 2 );
				auto ret = arguments[1]->free_variables( );
				ret.erase( arguments[0] );
				return ret;
			}
			else
			{
				std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > ret;
				std::transform( arguments.begin( ), arguments.end( ),
												set_inserter< term >( ret ), [&]( const std::shared_ptr< term > & t ){ return t->free_variables( ); } );
				return ret;
			}
		}
		std::set< function > functions( )
		{
			if ( name == "variable" ) { return { }; }
			else if ( name == "constant" ) { return { }; }
			else if ( is_quantifiers( ) ) { return arguments[1]->functions( ); }
			else
			{
				std::set< function > ret( { function( name, arity( ) ) } );
				std::for_each( arguments.begin( ), arguments.end( ),
											 [&]( const std::shared_ptr< term > & t )
				{
					auto func = t->functions( );
					std::for_each( func.begin( ), func.end( ), [&]( const function & t ){ ret.insert( t ); } );
				} );
				return ret;
			}
		}
		bool operator == ( const term & comp ) const { return ! ( * this < comp ) && ! ( comp < * this ); }
		std::shared_ptr< term > rebound( const std::shared_ptr< term > & old_term, const std::shared_ptr< term > & new_term )
		{
			if ( name == "variable" )
			{
				if ( * old_term == * this ) { return new_term; }
				else { return shared_from_this( ); }
			}
			else if ( name == "constant" ) { return shared_from_this( ); }
			else if ( is_quantifiers( ) && * old_term == * arguments[0] )
			{
				assert( arity( ) == 2 );
				return arguments[1]->rebound( old_term, new_term );
			}
			else
			{
				std::vector< std::shared_ptr< term > > ret;
				std::transform( arguments.begin( ), arguments.end( ), std::back_inserter( ret ), [&]( const std::shared_ptr< term > & t ){ return t->rebound( old_term, new_term ); } );
				return std::shared_ptr< term >( new term( name, ret ) );
			}
		}

		struct term_generator
		{
			size_t arity;
			std::map
			<
				std::shared_ptr< term >,
				std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >,
				value_less< std::shared_ptr< term > >
			> & cv;
			std::map
			<
				std::shared_ptr< term >,
				std::pair< term_generator, term_generator >,
				value_less< std::shared_ptr< term > >
			> term_map;
			std::set
			<
				std::shared_ptr< term >,
				value_less< std::shared_ptr< term > >
			> & functions;
			term_generator( size_t arity, decltype( cv ) & cv, decltype( functions ) & functions ) : arity( arity ), cv( cv ), functions( functions ) { }
			decltype( term_map.begin( ) ) i;

			std::vector< std::shared_ptr< term > > generate( decltype( term_map.begin( ) ) it )
			{
				auto f = it->second.first.generate( );
				auto s = it->second.second.generate( );
				f.reserve( f.size( ) + s.size( ) );
				std::copy( s.begin( ), s.end( ), std::back_inserter( f ) );
				return f;
			}

			term_generator generate_term_generator( size_t a ) { return term_generator( a, cv, functions ); }

			std::vector< std::shared_ptr< term > > generate( )
			{
				if ( arity == 0 ) { return { }; }
				else
				{
					for ( auto it : cv )
					{
						if ( term_map.count( it.first ) == 0 )
						{
							term_map.insert( std::make_pair(
																					 it.first,
																					 std::make_pair(
																						 generate_term_generator( arity - 1 ),
																						 generate_term_generator( it.first->arity( ) ) ) ) );
							return generate( term_map.find( it.first ) );
						}
					}
					for ( auto it : functions )
					{
						if ( term_map.count( it ) == 0 )
						{
							term_map.insert( std::make_pair(
																 it,
																 std::make_pair(
																	 generate_term_generator( arity - 1 ),
																	 generate_term_generator( it->arity( ) ) ) ) );
							return generate( term_map.find( it ) );
						}
					}
					if ( i == term_map.end( ) ) { }
					i = term_map.begin( );
					auto ret = generate( i );
					++i;
					return ret;
				}
			}
		};

		struct deduction_tree
		{
			std::shared_ptr< term > new_variable( )
			{
				auto ret = make_variable( std::to_string( unused++ ) );
				term_map.insert( std::make_pair( ret,  std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >( ) ) );
				return ret;
			}
			std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > sequent;
			std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > temp_sequent;
			std::map
			<
				std::shared_ptr< term >,
				std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >,
				value_less< std::shared_ptr< term > >
			> term_map;
			std::map< std::shared_ptr< term >, bool, value_less< std::shared_ptr< term > > > expanded;
			size_t unused = 0;
			std::set
			<
				std::shared_ptr< term >,
				value_less< std::shared_ptr< term > >
			> functions;
			term_generator tg;
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
							term_map.insert( std::make_pair( f[0], std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >( ) ) );
						}
						while ( ! sequent.empty( ) )
						{
							auto t = * sequent.begin( );
							sequent.erase( sequent.begin( ) );
							if ( t.first->name == "variable" ) { try_insert( expanded, t.first, t.second ); }
							else if ( t.first->name == "constant" ) { throw std::runtime_error( "invalid sequent." ); }
							else if ( t.first->is_quantifiers( ) )
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
								else
								{
									try_insert( expanded, t.first, t.second );
								}
							}
						}
					}
					return false;
				}
				catch ( contradiction & ) { return true; }
			}
			static std::shared_ptr< term > make_function( const std::string & s, const std::vector< std::shared_ptr< term > > & t )
			{ return std::shared_ptr< term >( new term( s, t ) ); }

			static std::shared_ptr< term > make_constant( const std::string & s )
			{ return std::shared_ptr< term >( new term( std::string( "constant" ), { std::shared_ptr< term >( new term( s, { } ) ) } ) ); }

			static std::shared_ptr< term > make_not( const std::shared_ptr< term > & s )
			{ return std::shared_ptr< term >( new term( std::string( "not" ), { s } ) ); }

			static std::shared_ptr< term > make_and( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
			{ return std::shared_ptr< term >( new term( std::string( "and" ), { l, r } ) ); }

			static std::shared_ptr< term > make_or( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
			{ return std::shared_ptr< term >( new term( std::string( "or" ), { l, r } ) ); }

			static std::shared_ptr< term > make_imply( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
			{ return make_or( make_not( l ), r ); }

			static std::shared_ptr< term > make_all( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
			{ return std::shared_ptr< term >( new term( std::string( "all" ), { l, r } ) ); }

			static std::shared_ptr< term > make_variable( const std::string & s )
			{ return std::shared_ptr< term >( new term( std::string( "variable" ), { std::shared_ptr< term >( new term( s, { } ) ) } ) ); }

			static std::shared_ptr< term > make_some( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
			{ return std::shared_ptr< term >( new term( std::string( "some" ), { l, r } ) ); }

			deduction_tree( const deduction_tree & t ) :
				sequent( t.sequent ),
				temp_sequent( t.temp_sequent ),
				term_map( t.term_map ),
				expanded( t.expanded ),
				unused( t.unused ),
				functions( t.functions ),
				tg( 1, term_map, functions ) { }
			deduction_tree( const std::shared_ptr< term > & t ) : sequent( { { t, false } } ), tg( 1, term_map, functions )
			{
				const auto fv = t->free_variables( );
				const auto con = t->constants( );
				const auto func = t->functions( );
				auto r = boost::range::join( boost::make_iterator_range( fv.begin( ), fv.end( ) ), boost::make_iterator_range( con.begin( ), con.end( ) ) );
				std::transform( r.begin( ), r.end( ), std::inserter( term_map, term_map.begin( ) ), [ ]( const std::shared_ptr< term > & s )
				{ return std::make_pair( s, std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > >( ) ); } );
				if ( term_map.empty( ) ) { new_variable( ); }
			}
		};

		bool is_valid( )
		{
			deduction_tree t( shared_from_this( ) );
			return t.is_valid( );
		}

		bool operator < ( const term & comp ) const
		{
			if ( name < comp.name ) { return true; }
			else if ( comp.name < name ) { return false; }
			else
			{
				if ( arity( ) < comp.arity( ) ) { return true; }
				else if ( comp.arity( ) < arity( ) ) { return false; }
				else
				{
					size_t i = 0;
					while ( i < arity( ) )
					{
						if ( * arguments[i] < * comp.arguments[i] ) { return true; }
						else if ( * comp.arguments[i] < * arguments[i] ) { return false; }
						++i;
					}
					return false;
				}
			}
		}
	};
}
#endif //GENTZEN_SYSTEM_FIRST_ORDER_LOGIC
