#ifndef RESOLUTION_HPP
#define RESOLUTION_HPP
#include "sentence.hpp"
#include "term.hpp"
namespace first_order_logic
{
	struct resolution
	{
		std::set< std::set< term > > s;
		resolution( const sentence & sen )
		{

		}
	};
	proposition move_negation_in( const proposition & prop )
	{
		if ( prop->is_atom ) { return prop; }
		else
		{
			auto & comb = boost::get< proposition_combine< proposition > >( prop->data );
			if ( comb.s == logical_not )
			{
				auto & in = comb.p.first;
				if ( in->is_atom ) { return prop; }
				else
				{
					auto & in_comb = boost::get< proposition_combine< proposition > >( in->data );
					if ( in_comb.s == logical_or )
					{ return make_and( move_negation_in( make_not( in_comb.p.first ) ), move_negation_in( make_not( in_comb.p.second ) ) ); }
					else if ( in_comb.s == logical_and )
					{ return make_or(
									move_negation_in( make_not( in_comb.p.first ) ),
									move_negation_in( make_not( in_comb.p.second ) ) ); }
					else
					{
						assert( in_comb.s == logical_not );
						return move_negation_in( in_comb.p.first );
					}
				}
			}
			else if ( comb.s == logical_and ) { return make_and( move_negation_in( comb.p.first ), move_negation_in( comb.p.second ) ); }
			else
			{
				assert( comb.s == logical_or );
				return  make_or( move_negation_in( comb.p.first ), move_negation_in( comb.p.second ) );
			}
		}
	}
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
		std::string data;
		bool b;
		literal( const std::string & d, bool b ) : data( d ), b( b ) { }
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
	proposition move_or_in( const proposition & prop )
	{
		if ( prop->is_atom ) { return prop; }
		else
		{
			auto & comb = boost::get< proposition_combine< proposition > >( prop->data );
			if ( comb.s == logical_or )
			{
				auto f = move_or_in( comb.p.first );
				auto s = move_or_in( comb.p.second );
				if ( f->is_atom && s->is_atom ) { return make_or( f, s ); }
				else if (
							f->is_atom ||
							( boost::get< proposition_combine< proposition > >( f->data ).s != logical_and &&
								! s->is_atom ) )
				{ f.swap( s ); }
				auto fcomb = boost::get< proposition_combine< proposition > >( f->data );
				if ( fcomb.s == logical_or || fcomb.s == logical_not ) { return make_or( f, s ); }
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
	clause get_clause( const proposition & prop )
	{
		if ( prop->is_atom ) { return { literal( boost::get< std::string >( prop->data ), true ) }; }
		else
		{
			auto comb = boost::get< proposition_combine< proposition > >( prop->data );
			if ( comb.s == logical_or )
			{
				auto cf = get_clause( comb.p.first );
				auto cs = get_clause( comb.p.second );
				std::copy( cf.data.begin( ), cf.data.end( ), std::inserter( cs.data, cs.data.end( ) ) );
				return cs;
			}
			else
			{
				assert( comb.s == logical_not );
				assert( comb.p.first->is_atom );
				return
				{
					literal(
								boost::get< std::string >( comb.p.first->data ),
								false )
				};
			}
		}
	}
	std::set< clause > flatten( const proposition & prop )
	{
		if ( prop->is_atom ) { return { clause( { literal( boost::get< std::string >( prop->data ), true ) } ) }; }
		else
		{
			auto comb = boost::get< proposition_combine< proposition > >( prop->data );
			if ( comb.s == logical_and )
			{
				auto cf = flatten( comb.p.first );
				auto cs = flatten( comb.p.second );
				std::copy( cf.begin( ), cf.end( ), std::inserter( cs, cs.end( ) ) );
				return cs;
			}
			else { return { get_clause( prop ) }; }
		}
	}

	proposition pre_CNF( const proposition & prop ) { return move_or_in( move_negation_in( prop ) ); }

	CNF to_CNF( const proposition & prop )
	{
		if ( prop->is_atom ) { return CNF ( { clause ( { literal( boost::get< std::string >( prop->data ), true ) } ) } ); }
		else { return CNF( flatten( pre_CNF( prop ) ) ); }
	}

}
#endif // RESOLUTION_HPP
