#ifndef FIRST_ORDER_LOGIC_SENTENCE_PREDICATE_HPP
#define FIRST_ORDER_LOGIC_SENTENCE_PREDICATE_HPP
#include <string>
namespace first_order_logic
{
    struct predicate
    {
        std::string name;
        size_t arity;
        predicate( const std::string & name, size_t arity ) : name( name ), arity( arity ) { }
        bool operator < ( const predicate & f ) const
        { return name < f.name || ( name == f.name && arity < f.arity ); }
    };
}
#endif //FIRST_ORDER_LOGIC_SENTENCE_PREDICATE_HPP
