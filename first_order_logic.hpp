#ifndef FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "sentence.hpp"
#include "atomic_sentence.hpp"
#include "term.hpp"
#include "variable.hpp"
#include "forward/first_order_logic.hpp"
#include "sentence_helper.hpp"
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
}
#endif //FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
