#ifndef FORWARD_FIRST_ORDER_LOGIC_H
#define FORWARD_FIRST_ORDER_LOGIC_H
#include <string>
#include <vector>
namespace first_order_logic
{
	struct term;
	struct sentence;
	struct variable;
	term make_function( const std::string & s, const std::vector< term > & t );
	term make_constant( const std::string & s );
	term make_variable( const std::string & s );
	sentence make_predicate( const std::string & s, const std::vector< term > & t );
	sentence make_propositional_letter( const std::string & s );
	sentence make_not( const sentence & s );
	sentence make_and( const sentence & l, const sentence & r );
	sentence make_or( const sentence & l, const sentence & r );
	sentence make_imply( const sentence & l, const sentence & r );
	sentence make_iff( const sentence & l, const sentence & r );
	sentence make_all( const variable & l, const sentence & r );
	sentence make_some( const variable & l, const sentence & r );
	sentence make_equal( const term & l, const term & r );
}
#endif // FORWARD_FIRST_ORDER_LOGIC_H
