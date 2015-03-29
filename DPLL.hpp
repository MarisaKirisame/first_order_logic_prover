#ifndef DPLL_HPP
#define DPLL_HPP
#include "resolution.hpp"
#include <algorithm>
#include <map>
#include <cassert>
#include <boost/variant.hpp>
namespace first_order_logic
{
    template< typename OUTITER >
    OUTITER find_pure_symbol( const std::list< std::list< literal > > & cnf, OUTITER out ) { return out; }
    template< typename OUTITER >
    OUTITER find_unit_clause( const std::list< std::list< literal > > & cnf, OUTITER out ) { return out; }
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
    bool DPLL( const std::list< std::list< literal > > & cnf, std::vector< std::pair< atomic_sentence, bool > > optimize )
    {
        if ( ! optimize.empty( ) )
        {
            auto ret = optimize.back( );
            optimize.pop_back( );
            return DPLL( substitute( cnf, ret.first, ret.second ), std::move( optimize ) );
        }
        else
        {
            if ( cnf.empty( ) ) { return true; }
            if ( std::any_of( cnf.begin( ), cnf.end( ), []( const auto & p ){ return p.empty( ); } ) ) { return false; }
            find_pure_symbol( cnf, std::back_inserter( optimize ) );
            find_unit_clause( cnf, std::back_inserter( optimize ) );
            if ( ! optimize.empty( ) ) { return DPLL( cnf, std::move( optimize ) ); }
            assert( cnf.begin( )->begin( ) != cnf.begin( )->end( ) );
            return
                DPLL( substitute( cnf, cnf.begin( )->begin( )->as, true ), optimize ) ||
                DPLL( substitute( cnf, cnf.begin( )->begin( )->as, false ), optimize );
        }
    }
    bool DPLL( const std::list< std::list< literal > > & cnf ) { return DPLL( cnf, { } ); }
}
#endif // DPLL_HPP
