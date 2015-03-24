#ifndef WALKSAT_HPP
#define WALKSAT_HPP
#include <random>
#include <iterator>
#include "CNF.hpp"
namespace first_order_logic
{
    template< typename T, typename RD >
    bool WALKSAT( const CNF & cnf, double p, T max_count, RD & rd )
    {
        std::map< atomic_sentence, bool > ass;
        for ( const clause & cl : cnf.data )
        {
            for ( const literal & l : cl.data )
            {
                if ( ass.count( l.data ) == 0 )
                { ass.insert( { l.data, std::uniform_int_distribution<>( 0, 1 )( rd ) } ); }
            }
        }
        if ( ass.empty( ) ) { return true; }
        auto conflict_number =
            [&]( )->size_t
            {
                return std::accumulate(
                    cnf.data.begin( ),
                    cnf.data.end( ),
                    static_cast< size_t >( 0 ),
                    [&]( size_t s, const clause & cl )->size_t
                    {
                        return
                            s +
                            (std::any_of(
                                cl.data.begin( ),
                                cl.data.end( ),
                                [&]( const literal & l )
                                {
                                    auto it = ass.find( l.data );
                                    assert( it != ass.end( ) );
                                    return it->second == l.b;
                                } ) ? 0 : 1);
                    } );
            };
        while ( max_count > 0 )
        {
            if ( conflict_number( ) == 0 ) { return true; }
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
        return false;
    }
}
#endif // WALKSAT_HPP
