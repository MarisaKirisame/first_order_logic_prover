#ifndef THEOREM_PROVER_PROPOSITIONAL_LOGIC_PROPOSITION
#define THEOREM_PROVER_PROPOSITIONAL_LOGIC_PROPOSITION
#include <map>
#include <memory>
#include <utility>
#include <cassert>
#include <vector>
#include <boost/variant.hpp>
#include "deduction_tree.hpp"
#include <set>
#include "initializer_list"
#include <algorithm>
#include "value_less.hpp"
#include "propositional_combine.hpp"
#include "propositional_letter.hpp"
namespace theorem_prover
{
	namespace propositional_logic
	{
		struct proposition : std::enable_shared_from_this< proposition >
		{
			boost::variant< propositional_letter, proposition_combine< const std::shared_ptr< proposition > > > data;
			bool is_atom;
			proposition( std::string && str ) : data( propositional_letter( std::move( str ) ) ), is_atom( true ) { }
			proposition( symbol s, std::pair< const std::shared_ptr< proposition >, const std::shared_ptr< proposition > > && p ) :
				data( proposition_combine< const std::shared_ptr< proposition > >( s, std::move( p ) ) ), is_atom( false ) { }
			bool is_satisfiable( )
			{
				deduction_tree< proposition > et( std::map< const std::shared_ptr< proposition >, bool, value_less< std::shared_ptr< proposition > > >( { std::make_pair( shared_from_this( ), true ) } ) );
				return et.is_satisfiable( );
			}

			bool is_falsifiable( )
			{
				deduction_tree< proposition > et( std::map< const std::shared_ptr< proposition >, bool, value_less< std::shared_ptr< proposition > > >( { std::make_pair( shared_from_this( ), false ) } ) );
				return et.is_satisfiable( );
			}

			satisfiability get_satisfiability( )
			{
				if ( is_satisfiable( ) )
				{
					if ( is_falsifiable( ) ) { return satisfiable; }
					else { return valid; }
				}
				else
				{ return unsatisfiable; }
			}
			static std::shared_ptr< proposition > make_or( const std::shared_ptr< proposition > & lhs, const std::shared_ptr< proposition > & rhs )
			{ return std::shared_ptr< proposition >( new proposition( logical_or, std::make_pair( lhs, rhs ) ) ); }
			static std::shared_ptr< proposition > make_and( const std::shared_ptr< proposition > & lhs, const std::shared_ptr< proposition > & rhs )
			{ return std::shared_ptr< proposition >( new proposition( logical_and, std::make_pair( lhs, rhs ) ) ); }
			static std::shared_ptr< proposition > make_not( const std::shared_ptr< proposition > & hs )
			{ return std::shared_ptr< proposition >( new proposition( logical_not, std::make_pair( hs, nullptr ) ) ); }
			static std::shared_ptr< proposition > make_equal( const std::shared_ptr< proposition > & lhs, const std::shared_ptr< proposition > & rhs )
			{ return make_or( make_and( lhs, rhs ), make_and( make_not( lhs ), make_not( rhs ) ) ); }
			static std::shared_ptr< proposition > make_imply( const std::shared_ptr< proposition > & lhs, const std::shared_ptr< proposition > & rhs )
			{ return make_or( make_not( lhs ), rhs ); }
			bool operator < ( const proposition & comp ) const
			{
				if ( is_atom < comp.is_atom ) { return true; }
				else if ( comp.is_atom < is_atom ) { return false; }
				else if ( is_atom ) { return boost::get< propositional_letter >( data ) < boost::get< propositional_letter >( comp.data ); }
				else
				{
					auto comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( data );
					auto comp_comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( comp.data );
					if ( comb.s < comp_comb.s ) { return true; }
					else if ( comp_comb.s < comb.s ) { return false; }
					else
					{
						if ( comb.s == logical_not ) { return * comb.p.first < * comp_comb.p.first; }
						else
						{
							if ( * comb.p.first < * comp_comb.p.first ) { return true; }
							else if ( * comp_comb.p.first < * comb.p.first ) { return true; }
							else { return * comb.p.second < * comp_comb.p.second; }
						}
					}
				}
			}
		};
	}
}
#endif //THEOREM_PROVER_PROPOSITIONAL_LOGIC_PROPOSITION
