#ifndef FIRST_ORDER_LOGIC_SAT_WALKSAT_HPP
#define FIRST_ORDER_LOGIC_SAT_WALKSAT_HPP
#include <random>
#include <iterator>
#include "satisfiability.hpp"
namespace first_order_logic
{
    template< typename T, typename RD >
    satisfiability WALKSAT( const std::list< std::list< literal > > & cnf, double p, T max_count, RD & rd )
    {
        std::map< atomic_sentence, bool > ass;
        for ( const auto & cl : cnf )
        {
            for ( const literal & l : cl )
            {
                if ( ass.count( l.as ) == 0 )
                { ass.insert( { l.as, std::uniform_int_distribution<>( 0, 1 )( rd ) } ); }
            }
        }
        if ( ass.empty( ) ) { return satisfiability::satisfiable; }
        auto conflict_number =
            [&]( )->size_t
            {
                return std::accumulate(
                    cnf.begin( ),
                    cnf.end( ),
                    static_cast< size_t >( 0 ),
                    [&]( size_t s, const auto & cl )->size_t
                    {
                        return
                            s +
                            (std::any_of(
                                cl.begin( ),
                                cl.end( ),
                                [&]( const literal & l )
                                {
                                    auto it = ass.find( l.as );
                                    assert( it != ass.end( ) );
                                    return it->second == l.b;
                                } ) ? 0 : 1);
                    } );
            };
        while ( max_count > 0 )
        {
            if ( conflict_number( ) == 0 ) { return satisfiability::satisfiable; }
            --max_count;
            if ( p > std::uniform_real_distribution<>( 0, 1 )( rd ) )
            {
                auto it = ass.begin( );
                std::advance( it, std::uniform_int_distribution<>( 0, ass.size( ) - 1 )( rd ) );
                it->second = ! it->second;
            }
            else
            {
                std::map< atomic_sentence, size_t > flip_value;
                for ( auto it = ass.begin( ); it != ass.end( ); ++it )
                {
                    it->second = ! it->second;
                    flip_value.insert( std::make_pair( it->first, conflict_number( ) ) );
                    it->second = ! it->second;
                }
                assert( flip_value.size( ) == ass.size( ) );
                auto it = std::min_element(
                            flip_value.begin( ),
                            flip_value.end( ),
                            []( const std::pair< atomic_sentence, size_t > & l,
                                const std::pair< atomic_sentence, size_t > & r ) { return l.second < r.second; } );
                it->second = ! it->second;
            }
        }
        return satisfiability::unsatisfiable;
    }
}
#endif //FIRST_ORDER_LOGIC_SAT_WALKSAT_HPP
