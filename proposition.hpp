#ifndef GENTZEN_SYSTEM_PROPOSITION
#define GENTZEN_SYSTEM_PROPOSITION
#include <iostream>
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
namespace gentzen_system
{
	struct proposition
	{
		boost::variant< propositional_letter, proposition_combine< const std::shared_ptr< proposition > > > data;
		bool is_atom;
		proposition( std::string && str ) : data( propositional_letter( std::move( str ) ) ), is_atom( true ) { }
		proposition( symbol s, std::pair< const std::shared_ptr< proposition >, const std::shared_ptr< proposition > > && p ) :
			data( proposition_combine< const std::shared_ptr< proposition > >( s, std::move( p ) ) ), is_atom( false ) { }
		static bool is_satisfiable( std::map< const std::shared_ptr< proposition >, bool > && t )
		{
			deduction_tree< proposition > et( move( t ) );
			return et.is_satisfiable( );
		}
		static satisfiability get_satisfiability( const std::shared_ptr< proposition > & prop )
		{
			if ( is_satisfiable( std::map< const std::shared_ptr< proposition >, bool >( { std::make_pair( prop, true ) } ) ) )
			{
				if ( is_satisfiable( std::map< const std::shared_ptr< proposition >, bool >( { std::make_pair( prop, false ) } ) ) )
				{ return satisfiable; }
				else
				{ return valid; }
			}
			else
			{ return unsatisfiable; }
		}
	};

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

	template< typename t >
	struct conjunction
	{
		std::set< t > data;
		conjunction( std::initializer_list< t > d ) : data( d ) { }
		conjunction( std::set< t > && d ) : data( std::move( d ) ) { }
	};

	template< typename t >
	struct disjunction
	{
		std::set< t > data;
		disjunction( std::initializer_list< t > d ) : data( d ) { }
		bool operator < ( const disjunction & comp ) const { return data < comp.data; }
		bool operator == ( const disjunction & comp ) const { return data == comp.data; }
	};

	struct literal
	{
		propositional_letter data;
		bool is_negation;
		literal( const propositional_letter & d, bool b ) : data( d ), is_negation( b ) { }
		bool operator < ( const literal & comp ) const { return data < comp.data || ( data == comp.data && is_negation < comp.is_negation ); }
		bool operator == ( const literal & comp ) const { return data == comp.data && is_negation == comp.is_negation; }
	};

	typedef disjunction< literal > clause;
	typedef conjunction< clause > CNF;

	std::shared_ptr< proposition > move_negation_in( const std::shared_ptr< proposition > & prop )
	{
		if ( prop->is_atom ) { return prop; }
		else
		{
			auto & comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( prop->data );
			if ( comb.s == logical_not )
			{
				auto & in = comb.p.first;
				if ( in->is_atom ) { return prop; }
				else
				{
					auto & in_comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( in->data );
					if ( in_comb.s == logical_or ) { return make_and( move_negation_in( make_not( in_comb.p.first ) ), move_negation_in( make_not( in_comb.p.second ) ) ); }
					else if ( in_comb.s == logical_and ) { return make_or( move_negation_in( make_not( in_comb.p.first ) ), move_negation_in( make_not( in_comb.p.second ) ) ); }
					else { return move_negation_in( in_comb.p.first ); }
				}
			}
			else { return prop; }
		}
	}

	std::shared_ptr< proposition > move_or_in( const std::shared_ptr< proposition > & prop )
	{
		if ( prop->is_atom ) { return prop; }
		else
		{
			auto & comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( prop->data );
			if ( comb.s == logical_or )
			{
				auto f = move_or_in( comb.p.first );
				auto s = move_or_in( comb.p.second );
				if ( f->is_atom && s->is_atom ) { return make_or( f, s ); }
				else if ( f->is_atom || ( boost::get< proposition_combine< const std::shared_ptr< proposition > > >( f->data ).s != logical_and && ! s->is_atom ) ) { f.swap( s ); }
				auto fcomb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( f->data );
				if ( fcomb.s == logical_or ) { return make_or( f, s ); }
				else
				{
					assert( fcomb.s == logical_and );
					return make_and( move_or_in( make_or( s, fcomb.p.first ) ), move_or_in( make_or( s, fcomb.p.second ) ) );
				}
			}
			else if ( comb.s == logical_and ) { return make_and( move_or_in( comb.p.first ), move_or_in( comb.p.second ) ); }
			else
			{
				assert( comb.s == logical_not );
				return make_not( move_or_in( comb.p.first ) );
			}
		}
	}

	clause get_clause( const std::shared_ptr< proposition > & prop )
	{
		if ( prop->is_atom ) { return { literal( boost::get< propositional_letter >( prop->data ), true ) }; }
		else
		{
			auto comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( prop->data );
			if ( comb.s == logical_or )
			{
				auto cf = get_clause( comb.p.first );
				auto cs = get_clause( comb.p.second );
				std::copy( cf.data.begin( ), cf.data.end( ), std::inserter( cs.data, cs.data.end( ) ) );
				return cf;
			}
			else
			{
				assert( comb.s == logical_not );
				return { literal( boost::get< propositional_letter >( prop->data ), false ) };
			}
		}
	}

	std::set< clause > flatten( const std::shared_ptr< proposition > & prop )
	{
		if ( prop->is_atom ) { return { clause( { literal( boost::get< propositional_letter >( prop->data ), true ) } ) }; }
		else
		{
			auto comb = boost::get< proposition_combine< const std::shared_ptr< proposition > > >( prop->data );
			if ( comb.s == logical_and )
			{
				auto cf = flatten( comb.p.first );
				auto cs = flatten( comb.p.second );
				std::copy( cf.begin( ), cf.end( ), std::inserter( cs, cs.end( ) ) );
				return cf;
			}
			else { return { get_clause( prop ) }; }
		}
	}

	CNF to_CNF( const std::shared_ptr< proposition > & prop )
	{
		if ( prop->is_atom ) { return CNF ( { clause ( { literal ( boost::get< propositional_letter >( prop->data ), true ) } ) } ); }
		else { return CNF( flatten( move_or_in( move_negation_in( prop ) ) ) ); }
	}
\
}
#endif //GENTZEN_SYSTEM_PROPOSITION
