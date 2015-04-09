#ifndef ATOMIC_SENTENCE_HPP
#define ATOMIC_SENTENCE_HPP
#include "term.hpp"
namespace first_order_logic
{
    struct atomic_sentence
    {
        std::string name;
        mutable std::string cache;
        std::vector< term > arguments;
        bool operator < ( const atomic_sentence & as ) const
        { return static_cast< std::string >( * this ) < static_cast< std::string >( as ); }
        bool operator == ( const atomic_sentence & as ) const
        { return static_cast< std::string >( * this ) == static_cast< std::string >( as ); }
        bool operator != ( const atomic_sentence & as ) const
        { return static_cast< std::string >( * this ) != static_cast< std::string >( as ); }
        explicit operator const std::string &( ) const
        {
            if ( ! cache.empty( ) ) { return cache; }
            std::string stack;
            auto it = arguments.begin( );
            while ( it != arguments.end( ) )
            {
                if ( it != arguments.begin( ) ) { stack += ", "; }
                stack += static_cast< std::string >( * it );
                ++it;
            }
            return cache = name + "(" + stack + ")";
        }
        explicit atomic_sentence( const std::string & str, const std::vector< term > & ter ) : name( str ), arguments( ter ) { }
    };

    template< typename OS >
    OS & operator << ( OS & os, const atomic_sentence & st )
    { return os << static_cast< std::string >( st ); }
}
#endif // ATOMIC_SENTENCE_HPP
