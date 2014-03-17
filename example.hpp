#pragma once
#include <iostream>
#include <map>
#include <memory>
#include <utility>
#include <cassert>
#include <vector>
namespace gentzen_system
{
	using namespace std;
	enum symbol
	{ logical_and, logical_or, logical_not, single_symbol };
	enum satisfiability
	{ valid, satisfiable, unsatisfiable };
	struct in_proposition
	{
		symbol s;
		pair< const shared_ptr< in_proposition >, const shared_ptr< in_proposition > > p;
		string str;
		in_proposition( string && str ) : s( single_symbol ), str( str ) { }
		in_proposition( symbol s, pair< const shared_ptr< in_proposition >, const shared_ptr< in_proposition > > && p ) : s( s ), p( p ) { }
	};
	struct proposition : shared_ptr< in_proposition >
	{
		struct insert_faliure{ };
		struct example_tree
		{
			map< const shared_ptr< in_proposition >, bool > sequent;
			map< string, bool > expanded_symbol;
			bool insert( const shared_ptr< in_proposition > p, bool b )
			{
				auto res = sequent.insert( make_pair( p, b ) );
				if ( ( ! res.second ) && res.first->second != b ) { return false; }
				return true;
			}
			example_tree( const map< const shared_ptr< in_proposition >, bool > & sequent, const map< string, bool > & expanded_symbol ) :
				sequent( sequent ), expanded_symbol( expanded_symbol ) { }
			example_tree( map< const shared_ptr< in_proposition >, bool > && sequent ) : sequent( sequent ) { }
			example_tree new_tree( const shared_ptr< in_proposition > p, bool b )
			{
				example_tree nt( sequent, expanded_symbol );
				if ( ! nt.insert( p, b ) ) { insert_faliure i_f; throw i_f; }
				return nt;
			}
			bool is_satisfiable( )
			{
				while ( ! sequent.empty( ) )
				{
					std::vector< bool > sb { false, true };
					for ( bool branching_allow : sb )
					{
						auto current_expand = sequent.begin( );
						const shared_ptr< in_proposition > prop = current_expand->first;
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
							else if ( branching_allow )
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
								if ( branching_allow )
								{
									try
									{
										if ( new_tree( prop->p.first, true ).is_satisfiable( ) )
										{ return true; }
									}
									catch ( insert_faliure & ) { }
									if ( ! insert( prop->p.second, true ) ) { return false; }
								}
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
				}
				return true;
			}
		};
		proposition( in_proposition * p ) : shared_ptr< in_proposition >( p ) { }
		satisfiability get_satisfiability( )
		{
			if ( is_satisfiable( map< const shared_ptr< in_proposition >, bool >( { make_pair( * this, true ) } ) ) )
			{
				if ( is_satisfiable( map< const shared_ptr< in_proposition >, bool >( { make_pair( * this, false ) } ) ) )
				{ return satisfiable; }
				else
				{ return valid; }
			}
			else
			{ return unsatisfiable; }
		}
		static bool is_satisfiable( map< const shared_ptr< in_proposition >, bool > && t )
		{
			example_tree et( move( t ) );
			return et.is_satisfiable( );
		}
	};

	static proposition make_or( const proposition & lhs, const proposition & rhs )
	{ return proposition( new in_proposition( logical_or, make_pair( lhs, rhs ) ) ); }
	static proposition make_and( const shared_ptr< in_proposition > lhs, const shared_ptr< in_proposition > rhs )
	{ return proposition( new in_proposition( logical_and, make_pair( lhs, rhs ) ) ); }
	static proposition make_not( const shared_ptr< in_proposition > hs )
	{ return proposition( new in_proposition( logical_not, make_pair( hs, nullptr ) ) ); }
	static proposition make_equal( const proposition & lhs, const proposition & rhs )
	{ return make_or( make_and( lhs, rhs ), make_and( make_not( lhs ), make_not( rhs ) ) ); }
	static proposition make_imply( const proposition & lhs, const proposition & rhs )
	{ return make_or( make_not( lhs ), rhs ); }

	int example( )
	{
		proposition A( new in_proposition( "A" ) );//A
		proposition B( new in_proposition( "B" ) );//B
		proposition C( new in_proposition( "C" ) );//C
		proposition not_a( make_not( A ) );//!A
		proposition valid_prop( make_or( A, not_a ) );//A or ! A( valid )
		proposition unsatisfiable_prop( make_and( A, not_a ) );
		proposition associativity_law_prop( make_imply( make_or( make_or( A, B ), C ), make_or( make_or( B, C ), A ) ) );
		auto res1 = A.get_satisfiability( );
		auto res2 = valid_prop.get_satisfiability( );
		auto res3 = unsatisfiable_prop.get_satisfiability( );
		if ( res1 == satisfiable && res2 == valid && res3 == unsatisfiable && make_equal( A, A ).get_satisfiability( ) == valid &&
				 make_and( make_not( make_imply( A, not_a ) ), not_a ).get_satisfiability( ) == unsatisfiable && associativity_law_prop.get_satisfiability( ) == valid )
		{ cout << "Hello World!" << endl; }
		return 0;
	}

}
