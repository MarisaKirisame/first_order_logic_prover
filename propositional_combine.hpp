#ifndef THEOREM_PROVER_PROPOSITIONAL_COMBINE
#define THEOREM_PROVER_PROPOSITIONAL_COMBINE
namespace theorem_prover
{
	enum class propositional_symbol
	{ logical_and, logical_or, logical_not };

	template< typename t >
	struct proposition_combine
	{
		propositional_symbol s;
		std::pair< t, t > p;
		proposition_combine( propositional_symbol s, std::pair< t, t > && p ) : s( s ), p( std::move( p ) ) { }
	};
}
#endif //THEOREM_PROVER_PROPOSITIONAL_COMBINE
