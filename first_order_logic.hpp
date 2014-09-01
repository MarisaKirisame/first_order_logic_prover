#ifndef FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "complex_sentence.hpp"
#include "complex_sentence.hpp"
#include "term.hpp"
namespace first_order_logic
{
	term make_function( const std::string & s, const std::vector< term > & t )
	{ return term( term::type::function, s, t ); }

	term make_constant( const std::string & s )
	{ return term( term::type::constant, s, { } ); }

	term make_variable( const std::string & s )
	{ return term( term::type::variable, s, { } ); }

	atomic_sentence make_predicate( const std::string & s, const std::vector< term > & t )
	{ return atomic_sentence( atomic_sentence::type::predicate, s, t ); }

	atomic_sentence make_propositional_letter( const std::string & s )
	{ return atomic_sentence( atomic_sentence::type::propositional_letter, s, { } ); }

	complex_sentence make_not( const complex_sentence & s )
	{ return complex_sentence( complex_sentence::type::logical_not, { s } ); }

	complex_sentence make_and( const complex_sentence & l, const complex_sentence & r )
	{ return complex_sentence( complex_sentence::type::logical_and, { l, r } ); }

	complex_sentence make_or( const complex_sentence & l, const complex_sentence & r )
	{ return complex_sentence( complex_sentence::type::logical_or, { l, r } ); }

	complex_sentence make_imply( const complex_sentence & l, const complex_sentence & r )
	{ return make_or( make_not( l ), r ); }

	complex_sentence make_iff( const complex_sentence & l, const complex_sentence & r )
	{ return make_or( make_and( l, r ), make_and( make_not( l ), make_not( r ) ) ); }

	complex_sentence make_all( const std::string & l, const complex_sentence & r )
	{ return complex_sentence( complex_sentence::type::all, make_variable( l ), r ); }

	complex_sentence make_some( const std::string & l, const complex_sentence & r )
	{ return complex_sentence( complex_sentence::type::some, make_variable( l ), r ); }

	atomic_sentence make_equal( const term & l, const term & r )
	{ return atomic_sentence( atomic_sentence::type::equal, "", { l, r } ); }
}
#endif //FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
