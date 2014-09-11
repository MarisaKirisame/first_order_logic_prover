#ifndef FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "sentence.hpp"
#include "term.hpp"
#include "variable.hpp"
namespace first_order_logic
{
	term make_function( const std::string & s, const std::vector< term > & t )
	{ return term( term::type::function, s, t ); }

	term make_constant( const std::string & s )
	{ return term( constant( s ) ); }

	term make_variable( const std::string & s )
	{ return term( variable( s ) ); }

	sentence make_predicate( const std::string & s, const std::vector< term > & t )
	{ return sentence( sentence::type::predicate, s, t ); }

	sentence make_propositional_letter( const std::string & s )
	{ return sentence( sentence::type::propositional_letter, s ); }

	sentence make_not( const sentence & s )
	{ return sentence( sentence::type::logical_not, { s } ); }

	sentence make_and( const sentence & l, const sentence & r )
	{ return sentence( sentence::type::logical_and, { l, r } ); }

	sentence make_or( const sentence & l, const sentence & r )
	{ return sentence( sentence::type::logical_or, { l, r } ); }

	sentence make_imply( const sentence & l, const sentence & r )
	{ return make_or( make_not( l ), r ); }

	sentence make_iff( const sentence & l, const sentence & r )
	{ return make_or( make_and( l, r ), make_and( make_not( l ), make_not( r ) ) ); }

	sentence make_all( const variable & l, const sentence & r )
	{ return sentence( sentence::type::all, l, r ); }

	sentence make_some( const variable & l, const sentence & r )
	{ return sentence( sentence::type::some, l, r ); }

	sentence make_equal( const term & l, const term & r )
	{ return sentence( sentence::type::equal, { l, r } ); }
}
#endif //FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
