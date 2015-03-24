#ifndef HORN_CLAUSES_H
#define HORN_CLAUSES_H
#include <set>
#include <memory>
#include <tuple>
#include <list>
namespace propositional_calculus
{
    struct horn_clauses
    {
        std::set< std::string > given;
        std::string imply;
        bool operator < ( const horn_clauses & comp ) const { return std::tie( given, imply ) < std::tie( comp.given, comp.imply ); }
    };
    bool forward_chaining( const std::list< horn_clauses > & l, const std::string & str )
    {
        std::map< horn_clauses, size_t > unproven_symbol_count;
        std::set< std::string > proven_symbol;
        std::list< std::string > add_list;
        for ( const horn_clauses & hc : l )
        {
            if ( hc.given.empty( ) ) { add_list.push_back( hc.imply ); }
            else { unproven_symbol_count.insert( { hc, hc.given.size( ) } ); }
        }
        while ( ! add_list.empty( ) )
        {
            const std::string & s = add_list.front( );
            if ( s == str ) { return true; }
            auto res = proven_symbol.insert( s );
            if ( res.second )
            {
                for ( auto it = unproven_symbol_count.begin( ); it != unproven_symbol_count.end( ); )
                {
                    --(it->second);
                    if ( it->second == 0 )
                    {
                        add_list.push_back( it->first.imply );
                        it = unproven_symbol_count.erase( it );
                    }
                    else { ++it; }
                }
            }
            add_list.pop_front( );
        }
        return false;
    }
}
#endif // HORN_CLAUSES_H
