#pragma once
#include <iostream>
#include <map>
#include <memory>
#include <utility>
#include <cassert>
namespace gentzen_system
{
	using namespace std;
	enum symbol
	{ logical_and, logical_or, logical_not, single_symbol };
	enum satisfiability
	{ valid, satisfiable, unsatisfiable };
	struct proposition
	{
		symbol s;
		pair< const proposition *, const proposition * > p;
		string str;
		struct insert_faliure{ };
		satisfiability get_satisfiability( ) const
		{
			if ( is_satisfiable( map< const proposition *, bool >( { make_pair( this, true ) } ) ) )
			{
				if ( is_satisfiable( map< const proposition *, bool >( { make_pair( this, false ) } ) ) )
				{ return satisfiable; }
				else
				{ return valid; }
			}
			else
			{ return unsatisfiable; }
		}
		struct example_tree
		{
			map< const proposition *, bool > sequent;
			map< string, bool > expanded_symbol;
			bool insert( const proposition * p, bool b )
			{
				auto res = sequent.insert( make_pair( p, b ) );
				if ( ( ! res.second ) && res.first->second != b ) { return false; }
				return true;
			}
			example_tree( const map< const proposition *, bool > & sequent, const map< string, bool > & expanded_symbol ) :
				sequent( sequent ), expanded_symbol( expanded_symbol ) { }
			example_tree( map< const proposition *, bool > && sequent ) : sequent( sequent ) { }
			example_tree new_tree( const proposition * p, bool b )
			{
				example_tree nt( sequent, expanded_symbol );
				if ( ! nt.insert( p, b ) ) { insert_faliure i_f; throw i_f; }
				return nt;
			}
			bool is_satisfiable( )
			{
				while ( ! sequent.empty( ) )
				{
					auto current_expand = sequent.begin( );
					const proposition * prop = current_expand->first;
					const bool need_satisfy = current_expand->second;
					sequent.erase( current_expand );
					if ( prop->s == single_symbol )
					{
						auto res = expanded_symbol.insert( make_pair( prop->str, need_satisfy ) );
						if ( ( ! res.second ) && res.first->second != need_satisfy ) { return false; }
					}
					else if ( prop->s == logical_and )
					{
						if ( current_expand->second )
						{
							if ( ( ! insert( prop->p.first, true ) ) ||
									 ( ! insert( prop->p.second, true ) ) )
							{ return false; }
						}
						else
						{
							try
							{
								if ( new_tree( prop->p.first, false ).is_satisfiable( ) )
								{ return true; }
							}
							catch ( insert_faliure & ) { }
							if ( ! insert( prop->p.second, false ) ) { return false; }
						}
					}
					else if ( prop->s == logical_or )
					{
						if ( current_expand->second )
						{
							try
							{
								if ( new_tree( prop->p.first, true ).is_satisfiable( ) )
								{ return true; }
							}
							catch ( insert_faliure & ) { }
							if ( ! insert( prop->p.second, true ) ) { return false; }
						}
						else
						{
							if ( ( ! insert( prop->p.first, false ) ) ||
									 ( ! insert( prop->p.second, false ) ) )
							{ return false; }
						}
					}
					else
					{ if ( ! insert( prop->p.first, ! need_satisfy ) ) { return false; } }
				}
				return true;
			}
		};
		static bool is_satisfiable( map< const proposition *, bool > && t )
		{
			example_tree et( move( t ) );
			return et.is_satisfiable( );
		}
		proposition( string && str ) : s( single_symbol ), str( str ) { }
		proposition( symbol s, pair< const proposition *, const proposition * > && p ) : s( s ), p( p ) { }
		static proposition make_or( const proposition & lhs, const proposition & rhs )
		{ return proposition( logical_or, make_pair( & lhs, & rhs ) ); }
		static proposition make_and( const proposition & lhs, const proposition & rhs )
		{ return proposition( logical_and, make_pair( & lhs, & rhs ) ); }
		static proposition make_not( const proposition & hs )
		{ return proposition( logical_not, make_pair( & hs, nullptr ) ); }
	};

	int example( )
	{
		proposition A( "A" );
		proposition not_a( proposition::make_not( A ) );
		auto res1 = A.get_satisfiability( );
		auto res2 = proposition::make_or( A, not_a ).get_satisfiability( );
		auto res3 = proposition::make_and( A, not_a ).get_satisfiability( );
		if ( res1 == satisfiable && res2 == valid && res3 == unsatisfiable )
		{ cout << "Hello World!" << endl; }
		return 0;
	}

}
