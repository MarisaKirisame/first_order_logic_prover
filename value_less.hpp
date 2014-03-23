#ifndef THEOREM_PROVER_VALUE_LESS
#define THEOREM_PROVER_VALUE_LESS
#include <memory>
namespace theorem_prover
{
	template< typename t >
	struct value_less;

	template< typename t >
	struct value_less< std::shared_ptr< t > >
	{ bool operator ( )( const std::shared_ptr< t > & lhs, const std::shared_ptr< t > & rhs ) const { return * lhs < * rhs; } };
}
#endif //THEOREM_PROVER_VALUE_LESS
