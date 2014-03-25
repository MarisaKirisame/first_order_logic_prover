#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_TERM
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_TERM
#include "deduction_tree.hpp"
#include "set_inserter.hpp"
namespace theorem_prover
{
	namespace first_order_logic
	{
		struct term : std::enable_shared_from_this< term >
		{
			std::string name;
			size_t arity( ) const { return arguments.size( ); }
			bool is_quantifier( ) const { return name == "some" || name == "all"; }
			std::vector< std::shared_ptr< term > > arguments;
			std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > constants( )
			{
				if ( name == "variable" )
				{
					assert( arity( ) == 1 );
					return { };
				}
				else if ( name == "constant" ) { return { shared_from_this( ) }; }
				else if ( is_quantifier( ) )
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
				else if ( is_quantifier( ) )
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

			bool have_equal( ) const
			{
				if ( name == "equal" ) { return true; }
				else
				{
					for ( auto i : arguments ) { if ( i->have_equal( ) ) { return true; } }
					return false;
				}
			}

			std::set< function > functions( )
			{
				if ( name == "variable" ) { return { }; }
				else if ( name == "constant" ) { return { }; }
				else if ( is_quantifier( ) ) { return arguments[1]->functions( ); }
				else
				{
					std::set< function > ret;
					if ( name != "and" && name != "or" && name != "not" && name != "equal" ) { ret.insert( function( name, arity( ) ) ); }
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
				else if ( is_quantifier( ) && * old_term == * arguments[0] )
				{
					assert( arity( ) == 2 );
					return arguments[1]->rebound( old_term, new_term );
				}
				else
				{
					std::vector< std::shared_ptr< term > > ret;
					std::transform( arguments.begin( ),
													arguments.end( ),
													std::back_inserter( ret ),
													[&]( const std::shared_ptr< term > & t ){ return t->rebound( old_term, new_term ); } );
					return std::shared_ptr< term >( new term( name, ret ) );
				}
			}

			bool is_valid( )
			{
				deduction_tree< term > t( shared_from_this( ) );
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
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_TERM
