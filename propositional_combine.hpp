#ifndef GENTZEN_SYSTEM_PROPOSITIONAL_COMBINE
#define GENTZEN_SYSTEM_PROPOSITIONAL_COMBINE
namespace gentzen_system
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
#endif //GENTZEN_SYSTEM_PROPOSITIONAL_COMBINE
