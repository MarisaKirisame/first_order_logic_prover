#pragma once
#include <iostream>
#include <map>
#include <memory>
#include <utility>
#include <cassert>
using namespace std;

struct proposition
{
    enum symbol
    {
        logical_and, logical_or, logical_not, single_symbol
    } s;
    pair< const proposition *, const proposition * > p;
    string str;
    enum satisfiability
    {
        valid, satisfiable, unsatisfiable
    };
    satisfiability get_satisfiability( ) const
    {
        if ( s == single_symbol )
        {
            return satisfiable;
        }
        else
        {
            bool res = is_satisfiable( map< const proposition *, bool >( { make_pair( this, true ) } ) );
            if ( res )
            {
                bool res = is_satisfiable( map< const proposition *, bool >( { make_pair( this, false ) } ) );
                if ( res )
                {
                    return satisfiable;
                }
                else
                {
                    return valid;
                }
            }
            else
            {
                return unsatisfiable;
            }
        }
    }
    static bool is_satisfiable( map< const proposition *, bool > && t )
    {
        auto tree( t );
        map< string, bool > expanded_symbol;
        while ( ! tree.empty( ) )
        {
            auto current_expand = tree.begin( );
            if ( current_expand->first->s == single_symbol )
            {
                auto res = expanded_symbol.insert( make_pair( current_expand->first->str, current_expand->second ) );
                if ( ( ! res.second ) && res.first->second != current_expand->second  ) { return false; }
                tree.erase( current_expand );
            }
            else if ( current_expand->first->s == logical_and )
            {
                if ( current_expand->second )
                {
                    auto res = tree.insert( make_pair( current_expand->first->p.first, true ) );
                    if ( ( ! res.second ) && ! res.first->second ) { return false; }
                    {
                        auto res = tree.insert( make_pair( current_expand->first->p.second, true ) );
                        if ( ( ! res.second ) && ! res.first->second ) { return false; }
                    }
                    tree.erase( current_expand );
                }
                else
                {
                    const proposition * original_prop = current_expand->first;
                    tree.erase( current_expand );
                    struct insert_faliure{ };
                    try {
                        if ( is_satisfiable( [ & ]( )->decltype( tree ) {
                                             auto new_tree( tree );
                                             auto res = new_tree.insert( make_pair( original_prop->p.first, false ) );
                                             if ( ( ! res.second ) && res.first->second ) { insert_faliure i_f; throw i_f; }
                                             return new_tree; } ( ) ) )
                        { return true; }
                    } catch ( insert_faliure & ) { }
                    auto res = tree.insert( make_pair( original_prop->p.second, false ) );
                    if ( ( ! res.second ) && res.first->second ) { return false; }
                }
            }
            else if ( current_expand->first->s == logical_or )
            {
                if ( current_expand->second )
                {
                    const proposition * original_prop = current_expand->first;
                    tree.erase( current_expand );
                    struct insert_faliure{ };
                    try {
                        if ( is_satisfiable( [ & ]( )->decltype( tree ) {
                                             auto new_tree( tree );
                                             auto res = new_tree.insert( make_pair( original_prop->p.first, true ) );
                                             if ( ( ! res.second ) && ! res.first->second ) { insert_faliure i_f; throw i_f; }
                                             return new_tree; } ( ) ) )
                        { return true; }
                    } catch ( insert_faliure & ) { }
                    auto res = tree.insert( make_pair( original_prop->p.second, true ) );
                    if ( ( ! res.second ) && ! res.first->second ) { return false; }
                }
                else
                {
                    auto res = tree.insert( make_pair( current_expand->first->p.first, false ) );
                    if ( ( ! res.second ) && res.first->second ) { return false; }
                    {
                        auto res = tree.insert( make_pair( current_expand->first->p.second, false ) );
                        if ( ( ! res.second ) && res.first->second ) { return false; }
                    }
                    tree.erase( current_expand );
                }
            }
            else
            {
                auto res = tree.insert( make_pair( current_expand->first->p.first, ! current_expand->second ) );
                if ( ( ! res.second ) && res.first->second == current_expand->second ) { return false; }
                tree.erase( current_expand );
            }
        }
        return true;
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
    if ( res1 == proposition::satisfiable && res2 == proposition::valid && res3 == proposition::unsatisfiable )
    { cout << "Hello World!" << endl; }
    return 0;
}

