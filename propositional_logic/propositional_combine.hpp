#ifndef THEOREM_PROVER_PROPOSITIONAL_PROPOSITIONAL_LOGIC_COMBINE
#define THEOREM_PROVER_PROPOSITIONAL_PROPOSITIONAL_LOGIC_COMBINE
#include <utility>
namespace theorem_prover
{
	namespace propositional_logic
	{
		enum symbol
		{ logical_and, logical_or, logical_not };

		template< typename t >
		struct proposition_combine
		{
			symbol s;
			std::pair< t, t > p;
			proposition_combine( symbol s, std::pair< t, t > && p ) : s( s ), p( std::move( p ) ) { }
		};
	}
}
#endif //THEOREM_PROVER_PROPOSITIONAL_PROPOSITIONAL_LOGIC_COMBINE
