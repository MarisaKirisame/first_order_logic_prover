#ifndef FIRST_ORDER_LOGIC_TERM
#define FIRST_ORDER_LOGIC_TERM
#include "deduction_tree.hpp"
#include "set_inserter.hpp"
#include "function.hpp"
#include "predicate.hpp"
#include "proof_tree.hpp"
#include <boost/optional.hpp>
namespace first_order_logic
{
	struct term
	{
		struct internal : std::enable_shared_from_this< internal >
		{
			std::string name;
			size_t arity( ) const { return arguments.size( ); }
			bool is_quantifier( ) const { return name == "some" || name == "all"; }
			std::vector< term > arguments;
			std::set< term > constants( )
			{
				if ( name == "variable" )
				{
					assert( arity( ) == 1 );
					return { };
				}
				else if ( name == "constant" ) { return { term( shared_from_this( ) ) }; }
				else if ( is_quantifier( ) )
				{
					assert( arity( ) == 2 );
					return arguments[1]->constants( );
				}
				else
				{
					std::set< term > ret;
					std::transform( arguments.begin( ), arguments.end( ), set_inserter< term >( ret ),
													[&]( const term & t ){ return t->constants( ); } );
					return ret;
				}
			}
			internal( const std::string & s, std::initializer_list< term > il ) : name( s ), arguments( il ) { }
			internal( const std::string & s, const std::vector< term > & il ) : name( s ), arguments( il ) { }
			size_t length( ) const
			{
				if ( name == "variable" ) { return 1; }
				else if ( name == "constant" ) { return 1; }
				else
				{
					return std::accumulate( arguments.begin( ),
											arguments.end( ),
											0,
											[&]( size_t s, const term & t ){ return s + t->length( ); } );
				}
			}
			std::set< term > free_variables( )
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
					std::set< term > ret;
					std::transform( arguments.begin( ),
									arguments.end( ),
									set_inserter< term >( ret ),
									[&]( const term & t ){ return t->free_variables( ); } );
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
			std::set< function > functions( bool met_predicate_before = false )
			{
				if ( name == "variable" ) { return { }; }
				else if ( name == "constant" ) { return { }; }
				else if ( is_quantifier( ) ) { return arguments[1]->functions( met_predicate_before ); }
				else
				{
					std::set< function > ret;
					bool function_or_predicate = ( name != "and" && name != "or" && name != "not" && name != "equal" );
					if ( function_or_predicate && met_predicate_before ) { ret.insert( function( name, arity( ) ) ); }
					std::for_each(
								arguments.begin( ),
								arguments.end( ),
								[&]( const term & t )
								{
									auto func = t->functions( met_predicate_before || function_or_predicate );
									std::for_each( func.begin( ), func.end( ), [&]( const function & t ){ ret.insert( t ); } );
								} );
					return ret;
				}
			}
			std::set< predicate > predicates( )
			{
				if ( name == "variable" ) { return { }; }
				else if ( name == "constant" ) { return { }; }
				else if ( is_quantifier( ) ) { return arguments[1]->predicates( ); }
				else
				{
					std::set< predicate > ret;
					if ( name != "and" && name != "or" && name != "not" && name != "equal" ) { ret.insert( predicate( name, arity( ) ) ); }
					else
					{
						std::for_each(
									arguments.begin( ),
									arguments.end( ),
									[&]( const term & t )
									{
										auto func = t->predicates( );
										std::for_each( func.begin( ), func.end( ), [&]( const predicate & t ){ ret.insert( t ); } );
									} );
					}
					return ret;
				}
			}
			bool operator == ( const internal & comp ) const { return ! ( * this < comp ) && ! ( comp < * this ); }
			term rebound( const term & old_term, const term & new_term )
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
					std::vector< term > ret;
					std::transform( arguments.begin( ),
									arguments.end( ),
									std::back_inserter( ret ),
									[&]( const term & t ){ return t->rebound( old_term, new_term ); } );
					return term( new internal( name, ret ) );
				}
			}
			bool operator < ( const internal & comp ) const
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
			explicit operator std::string( ) const
			{
				if ( name == "and" )
				{
					assert( arguments.size( ) == 2 );
					return "(" + static_cast< std::string >( * arguments[0] ) + "/\\" + static_cast< std::string >( * arguments[1] ) + ")";
				}
				else if ( name == "not" )
				{
					assert( arguments.size( ) == 1 );
					return std::string( "(" ) + "!" + static_cast< std::string >( * arguments[0] ) + ")";
				}
				else if ( name == "or" )
				{
					assert( arguments.size( ) == 2 );
					return "(" + static_cast< std::string >( * arguments[0] ) + "\\/" + static_cast< std::string >( * arguments[1] ) + ")";
				}
				else if ( name == "variable" || name == "constant" )
				{
					assert( arguments.size( ) == 1 );
					return arguments[0]->name;
				}
				else if ( name == "equal" )
				{
					assert( arguments.size( ) == 2 );
					return "(" + static_cast< std::string >( * arguments[0] ) + "=" + static_cast< std::string >( * arguments[1] ) + ")";
				}
				else if ( name == "all" )
				{
					assert( arguments.size( ) == 2 );
					return "∀" + static_cast< std::string >( * arguments[0] ) + " " + static_cast< std::string >( * arguments[1] );
				}
				else if ( name == "some" )
				{
					assert( arguments.size( ) == 2 );
					return "∃" + static_cast< std::string >( * arguments[0] ) + " " + static_cast< std::string >( * arguments[1] );
				}
				else
				{
					std::string stack;
					for ( const auto & i : arguments )
					{
						if( ! stack.empty( ) ) { stack += ", "; };
						stack += static_cast< std::string >( * i );
					}
					return name + "(" + stack + ")";
				}
				throw std::runtime_error( "unknown name : " + name );
			}
		};
		std::shared_ptr< internal > data;
		std::shared_ptr< proof_tree > pt;
		bool is_valid( )
		{
			deduction_tree< term > t( * this );
			bool res = t.is_valid( );
			pt = t.pt;
			return res;
		}
		internal * operator ->( ) const { return data.get( ); }
		internal & operator * ( ) const { return * data; }
		bool operator < ( const term & comp ) const
		{
			size_t l1 = (*this)->length( ), l2 = comp->length( );
			if ( l1 < l2 ) { return true; }
			if ( l2 < l1 ) { return false; }
			return * data < * comp.data;
		}
		term( const std::shared_ptr< internal > & ptr ) : data( ptr ) { }
		term( internal * ptr ) : data( ptr ) { }
		term( ) { }
		term & operator = ( const term & t )
		{
			data = t.data;
			pt = t.pt;
			return * this;
		}
	};
}
#endif //FIRST_ORDER_LOGIC_TERM
