#ifndef FIRST_ORDER_LOGIC_SAT_DPLL_HPP
#define FIRST_ORDER_LOGIC_SAT_DPLL_HPP
#include <algorithm>
#include <map>
#include <cassert>
#include <boost/variant.hpp>
#include "satisfiability.hpp"
#include "../cpp_common/iterator.hpp"
namespace first_order_logic
{
    template< typename OUTITER >
    OUTITER find_pure_symbol( const std::list< std::list< literal > > & cnf, OUTITER out )
    {
        auto ret = common::make_iterator_iterator( cnf.begin( ), cnf.end( ) );
        std::map< atomic_sentence, bool > map;
        for ( const auto & i : common::make_range_container_proxy( ret.first, ret.second ) ) { map.insert( { i.as, i.b } ); }
        for ( const auto & i : common::make_range_container_proxy( ret.first, ret.second ) )
        {
            auto it = map.find( i.as );
            if ( it != map.end( ) && ( it->second != i.b ) ) { map.erase( i.as ); }
        }
        for ( const auto & i : map )
        {
            *out = literal( i.first, i.second );
            ++out;
        }
        return out;
    }
    template< typename OUTITER >
    OUTITER find_unit_clause( const std::list< std::list< literal > > & cnf, OUTITER out )
    {
        for ( const auto & l : cnf )
        {
            if ( l.size( ) == 1 )
            {
                *out = l.front( );
                ++out;
            }
        }
        return out;
    }
    std::list< std::list< literal > > substitute( std::list< std::list< literal > > cnf, const atomic_sentence & as, bool with )
    {
        for ( auto it = cnf.begin( ); it != cnf.end( ); )
        {
            for ( auto iit = it->begin( ); iit != it->end( ); )
            {
                if ( iit->as == as )
                {
                    if ( iit->b == with )
                    {
                        it = cnf.erase( it );
                        goto http;
                    }
                    else { iit = it->erase( iit ); }
                }
                else { ++iit; }
            }
            ++it;
            http://marisa.moe
            { }
        }
        return cnf;
    }
    satisfiability DPLL( const std::list< std::list< literal > > & cnf, std::vector< literal > optimize )
    {
        if ( ! optimize.empty( ) )
        {
            auto ret = optimize.back( );
            optimize.pop_back( );
            return DPLL( substitute( cnf, ret.as, ret.b ), std::move( optimize ) );
        }
        else
        {
            if ( cnf.empty( ) ) { return satisfiability::satisfiable; }
            if ( std::any_of( cnf.begin( ), cnf.end( ), []( const auto & p ){ return p.empty( ); } ) ) { return satisfiability::unsatisfiable; }
            find_pure_symbol( cnf, std::back_inserter( optimize ) );
            find_unit_clause( cnf, std::back_inserter( optimize ) );
            if ( ! optimize.empty( ) ) { return DPLL( cnf, std::move( optimize ) ); }
            assert( cnf.begin( )->begin( ) != cnf.begin( )->end( ) );
            return
                (is_satisfiable( DPLL( substitute( cnf, cnf.begin( )->begin( )->as, true ), optimize ) ).value( ) ||
                is_satisfiable( DPLL( substitute( cnf, cnf.begin( )->begin( )->as, false ), optimize ) ).value( ) ) ?
                        satisfiability::satisfiable : satisfiability::unsatisfiable;
        }
    }
    satisfiability DPLL( const std::list< std::list< literal > > & cnf ) { return DPLL( cnf, { } ); }
}
#endif //FIRST_ORDER_LOGIC_SAT_DPLL_HPP
