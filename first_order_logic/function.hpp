#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_FUNCTION
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_FUNCTION
#include <string>
namespace theorem_prover
{
	namespace first_order_logic
	{
		struct function
		{
			std::string name;
			size_t arity;
			function( const std::string & name, size_t arity ) : name( name ), arity( arity ) { }
			bool operator < ( const function & f ) const { return name < f.name || ( name == f.name && arity < f.arity ); }
		};
	}
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_FUNCTION
