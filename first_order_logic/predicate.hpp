#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_PREDICATE_HPP
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_PREDICATE_HPP
#include <string>
namespace theorem_prover
{
	namespace first_order_logic
	{
		struct predicate
		{
			std::string name;
			size_t arity;
			predicate( const std::string & name, size_t arity ) : name( name ), arity( arity ) { }
			bool operator < ( const predicate & f ) const { return name < f.name || ( name == f.name && arity < f.arity ); }
		};
	}
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_PREDICATE_HPP
