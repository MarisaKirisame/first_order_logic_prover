#ifndef DPLL_HPP
#define DPLL_HPP
#include "CNF.hpp"
#include <algorithm>
#include <map>
#include <cassert>
#include <CNF.hpp>
#include <boost/variant.hpp>
namespace first_order_logic
{
    template< typename OUTITER >
    OUTITER find_pure_symbol( const CNF & cnf, OUTITER out ) { return out; }
    template< typename OUTITER >
    OUTITER find_unit_clause( const CNF & cnf, OUTITER out ) { return out; }
    CNF substitute( CNF cnf, const atomic_sentence & as, bool with )
    {
        for ( auto it = cnf.data.begin( ); it != cnf.data.end( ); )
        {
            for ( auto iit = it->data.begin( ); iit != it->data.end( ); )
            {
                if ( iit->data == as )
                {
                    if ( iit->b == with )
                    {
                        it = cnf.data.erase( it );
                        goto http;
                    }
                    else { iit = it->data.erase( iit ); }
                }
                else { ++iit; }
            }
            ++it;
            http://marisa.moe
            { }
        }
        return cnf;
    }
    bool DPLL( const CNF & cnf, std::vector< std::pair< atomic_sentence, bool > > optimize )
    {
        if ( ! optimize.empty( ) )
        {
            auto ret = optimize.back( );
            optimize.pop_back( );
            return DPLL( substitute( cnf, ret.first, ret.second ), std::move( optimize ) );
        }
        else
        {
            if ( cnf.data.empty( ) ) { return true; }
            if ( std::any_of( cnf.data.begin( ), cnf.data.end( ), []( const auto & p ){ return p.data.empty( ); } ) ) { return false; }
            find_pure_symbol( cnf, std::back_inserter( optimize ) );
            find_unit_clause( cnf, std::back_inserter( optimize ) );
            if ( ! optimize.empty( ) ) { return DPLL( cnf, std::move( optimize ) ); }
            assert( cnf.data.begin( )->data.begin( ) != cnf.data.begin( )->data.end( ) );
            return
                DPLL( substitute( cnf, cnf.data.begin( )->data.begin( )->data, true ), optimize ) ||
                DPLL( substitute( cnf, cnf.data.begin( )->data.begin( )->data, false ), optimize );
        }
    }
    bool DPLL( const CNF & cnf ) { return DPLL( cnf, { } ); }
}
#endif // DPLL_HPP
