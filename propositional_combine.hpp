#ifndef GENTZEN_SYSTEM_PROPOSITIONAL_COMBINE
#define GENTZEN_SYSTEM_PROPOSITIONAL_COMBINE
namespace gentzen_system
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
#endif //GENTZEN_SYSTEM_PROPOSITIONAL_COMBINE
