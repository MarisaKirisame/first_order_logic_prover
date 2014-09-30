#ifndef RESOLUTION_HPP
#define RESOLUTION_HPP
#include "sentence.hpp"
#include "term.hpp"
namespace first_order_logic
{
	template< typename t >
	struct conjunction
	{
		std::set< t > data;
		conjunction( std::initializer_list< t > d ) : data( d ) { }
		conjunction( std::set< t > && d ) : data( std::move( d ) ) { }
		conjunction( ) { }
	};
	template< typename t >
	struct disjunction
	{
		std::set< t > data;
		disjunction( std::initializer_list< t > d ) : data( d ) { }
		disjunction( ) { }
		bool operator < ( const disjunction & comp ) const { return data < comp.data; }
		bool operator == ( const disjunction & comp ) const { return data == comp.data; }
		struct join_faliure { };
		disjunction join( const disjunction & d ) const
		{
			if ( & d == this ) { throw join_faliure( ); }
			assert( d.data.size( ) < 1000 );
			assert( data.size( ) < 1000 );
			if ( d.data.size( ) < data.size( ) ) { return d.join( * this ); }
			std::set< t > conjugate_set;
			for ( auto i : data )
			{
				auto con = i.conjugate( );
				assert( d.data.size( ) < 1000 );
				assert( data.size( ) < 1000 );
				if ( d.data.find( con ) != d.data.end( ) )
				{ conjugate_set.insert( i ); }
			}
			if ( conjugate_set.size( ) != 1 ) { join_faliure jf; throw jf; }
			else
			{
				disjunction ret( d.data );
				std::copy( data.begin( ), data.end( ), std::inserter( ret.data, ret.data.begin( ) ) );
				ret.data.erase( * conjugate_set.begin( ) );
				ret.data.erase( conjugate_set.begin( )->conjugate( ) );
				return ret;
			}
		}
		disjunction( const std::set< t > & d ) : data( d ) { }
		disjunction( std::set< t > && d ) : data( std::move( d ) ) { }
	};
	struct literal
	{
		sentence data;
		bool b;
		literal( const sentence & d, bool b ) : data( d ), b( b ) { }
		bool operator < ( const literal & comp ) const { return std::tie( data, b ) < std::tie( comp.data, comp.b ); }
		bool operator == ( const literal & comp ) const { return std::tie( data, b ) == std::tie( comp.data, comp.b ); }
		literal conjugate( ) const
		{
			literal ret( * this );
			ret.b = ! ret.b;
			return ret;
		}
	};
	typedef disjunction< literal > clause;
	typedef conjunction< clause > CNF;
	sentence move_negation_in( const sentence & prop )
	{
		sentence se;
		prop.type_restore
		(
			make_not_actor(
				[&]( const sentence & sen )
				{
					sen.type_restore(
						make_not_actor( [&]( const sentence & sen ){ se = move_negation_in( sen ); } ),
						make_and_actor(
							[&]( const sentence & l, const sentence & r )
							{
								se = make_or(
										move_negation_in( make_not( l ) ),
										move_negation_in( make_not( r ) ) );
							} ),
						make_or_actor(
							[&]( const sentence & l, const sentence & r )
							{
								se = make_and(
										move_negation_in( make_not( l ) ),
										move_negation_in( make_not( r ) ) );
							} ),
						ignore( ) );
				} ),
			make_and_actor(
				[&]( const sentence & l, const sentence & r )
				{ se = make_and( move_negation_in( l ), move_negation_in( r ) ); } ),
			make_or_actor(
				[&]( const sentence & l, const sentence & r )
				{ se = make_or( move_negation_in( l ), move_negation_in( r ) ); } ),
			ignore( )
		);
		return se ? se : prop;
	}
	sentence move_or_in( const sentence & prop )
	{
		sentence se;
		prop.type_restore
		(
			make_not_actor( [&]( const sentence & sen ) { se = make_not( move_or_in( sen ) ); } ),
			make_and_actor(
				[&]( const sentence & l, const sentence & r ) { se = make_and( move_or_in( l ), move_or_in( r ) ); } ),
			make_or_actor(
				[&]( sentence l, sentence r )
				{
					if ( l.is_atom( ) || r.is_atom( ) )
					{
						se = make_or( l, r );
						return;
					}
					else if ( r->sentence_type == sentence::type::logical_and ) { l.swap( r ); }
					l.type_restore(
						make_and_actor(
							[&]( const sentence & ll, const sentence & rr )
							{
								se = make_and(
											move_or_in( make_or( r, ll ) ),
											move_or_in( make_or( r, rr ) ) );
							} ),
							ignore( ) );
					if ( ! se ) { se = make_or( l, r ); }
				} ),
			ignore( )
		);
		return se ? se : prop;
	}
	clause get_clause( const sentence & prop )
	{
		clause ret;
		prop.type_restore
				(
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							auto cf = get_clause( l );
							auto cs = get_clause( r );
							std::copy( cf.data.begin( ), cf.data.end( ), std::inserter( cs.data, cs.data.end( ) ) );
							ret = cs;
						} ),
					make_not_actor(
						[&]( const sentence & sen )
						{ ret = { literal( sen, false ) }; } ),
					ignore( )
				);
		if ( ret.data.empty( ) )
		{
			assert( prop.is_atom( ) );
			ret = { literal( prop, true ) };
		}
		return ret;
	}
	std::set< clause > flatten( const sentence & prop )
	{
		if ( prop.is_atom( ) ) { return { clause( { literal( prop, true ) } ) }; }
		else
		{
			std::set< clause > ret;
			prop.type_restore(
				make_and_actor(
					[&]( const sentence & l, const sentence & r )
					{
						auto cf = flatten( l );
						auto cs = flatten( r );
						std::copy( cf.begin( ), cf.end( ), std::inserter( cs, cs.end( ) ) );
						ret = cs;
					} ),
					ignore( ) );
			if ( ! ret.empty( ) ) { return ret; }
			else { return { get_clause( prop ) }; }
		}
	}

	sentence pre_CNF( const sentence & prop ) { return move_or_in( move_negation_in( prop ) ); }

	CNF to_CNF( const sentence & prop )
	{
		if ( prop.is_atom( ) ) { return CNF ( { clause ( { literal( prop, true ) } ) } ); }
		else { return CNF( flatten( pre_CNF( prop ) ) ); }
	}
	bool resolution( const sentence & sen, const sentence & goal )
	{
		CNF cnf(
				to_CNF(
					make_and( sen, make_not( goal ).restore_quantifier_existential( ) ).
						rectify( ).
						move_quantifier_out( ).
						skolemization_remove_existential( ).
						drop_universal( ) ) );
		std::set< clause > to_be_added;
		bool have_new_inference = true;
		while ( have_new_inference )
		{
			have_new_inference = false;
			for ( const clause & l : cnf.data )
			{
				for ( const clause & r : cnf.data )
				{
					for ( const literal & ll : l.data )
					{
						for ( const literal & rr : r.data )
						{
							if ( ll.b != rr.b )
							{
								auto un = unify( ll.data, rr.data );
								if ( un )
								{
									clause cl;
									for ( const literal & ins : l.data )
									{
										if ( (*un)(ins.data) != (*un)(ll.data) && (*un)(ins.data) != (*un)(rr.data) )
										{ cl.data.insert( literal( (*un)( ins.data ), ins.b ) ); }
									}
									for ( const literal & ins : r.data )
									{
										if ( (*un)(ins.data) != (*un)(ll.data) && (*un)(ins.data) != (*un)(rr.data) )
										{ cl.data.insert( literal( (*un)( ins.data ), ins.b ) ); }
									}
									if ( cl.data.empty( ) ) { return true; }
									to_be_added.insert( cl );
								}
							}
						}
					}
				}
			}
			for ( const clause & c : to_be_added )
			{
				auto res = cnf.data.insert( c );
				have_new_inference = have_new_inference || res.second;
			}
			to_be_added.clear( );
		}
		return false;
	}
}
#endif // RESOLUTION_HPP
