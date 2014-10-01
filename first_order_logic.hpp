#ifndef FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "sentence.hpp"
#include "atomic_sentence.hpp"
#include "term.hpp"
#include "variable.hpp"
#include "forward/first_order_logic.hpp"
namespace first_order_logic
{
	inline term make_function( const std::string & s, const std::vector< term > & t )
	{ return term( term::type::function, s, t ); }

	inline term make_constant( const std::string & s )
	{ return term( constant( s ) ); }

	inline term make_variable( const std::string & s )
	{ return term( variable( s ) ); }

	inline atomic_sentence make_predicate( const std::string & s, const std::vector< term > & t )
	{ return atomic_sentence( atomic_sentence::type::predicate, s, t ); }

	inline atomic_sentence make_propositional_letter( const std::string & s )
	{ return atomic_sentence( atomic_sentence::type::propositional_letter, s ); }

	inline sentence make_not( const sentence & s )
	{ return sentence( sentence::type::logical_not, { s } ); }

	inline sentence make_and( const sentence & l, const sentence & r )
	{ return sentence( sentence::type::logical_and, { l, r } ); }

	inline sentence make_or( const sentence & l, const sentence & r )
	{ return sentence( sentence::type::logical_or, { l, r } ); }

	inline sentence make_imply( const sentence & l, const sentence & r )
	{ return make_or( make_not( l ), r ); }

	inline sentence make_iff( const sentence & l, const sentence & r )
	{ return make_or( make_and( l, r ), make_and( make_not( l ), make_not( r ) ) ); }

	inline sentence make_all( const variable & l, const sentence & r )
	{ return sentence( sentence::type::all, l, r ); }

	inline sentence make_some( const variable & l, const sentence & r )
	{ return sentence( sentence::type::some, l, r ); }

	inline atomic_sentence make_equal( const term & l, const term & r )
	{ return atomic_sentence( atomic_sentence::type::equal, { l, r } ); }
}
#endif //FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
