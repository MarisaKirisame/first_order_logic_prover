#ifndef GENTZEN_SYSTEM_EXAMPLE
#define GENTZEN_SYSTEM_EXAMPLE
#include "proposition.hpp"
namespace gentzen_system
{
	int example( )
	{
		std::shared_ptr< proposition > A( new proposition( "A" ) );//A
		std::shared_ptr< proposition > B( new proposition( "B" ) );//B
		std::shared_ptr< proposition > C( new proposition( "C" ) );//C
		std::shared_ptr< proposition > not_a( make_not( A ) );//!A
		std::shared_ptr< proposition > valid_prop( make_or( A, not_a ) );//A or ! A( valid )
		std::shared_ptr< proposition > unsatisfiable_prop( make_and( A, not_a ) );
		std::shared_ptr< proposition > associativity_law_prop( make_equal( make_or( make_or( A, B ), C ), make_or( make_or( B, C ), A ) ) );
		std::shared_ptr< proposition > valid_prop2( make_imply( A, make_imply( B, A ) ) );
		auto res1 = A->get_satisfiability( A );
		auto res2 = valid_prop->get_satisfiability( valid_prop );
		auto res3 = unsatisfiable_prop->get_satisfiability( unsatisfiable_prop );
		auto cnf = to_CNF( unsatisfiable_prop );
		auto cnf2 = to_CNF( make_not( associativity_law_prop ) );
		auto cnf3 = to_CNF( associativity_law_prop );
		if (
				res1 == satisfiable &&
				res2 == valid &&
				res3 == unsatisfiable &&
				associativity_law_prop->get_satisfiability( associativity_law_prop ) == valid &&
				valid_prop2->get_satisfiability( valid_prop2 ) == valid &&
				is_unsatisfiable( cnf ) && is_unsatisfiable( cnf2 ) && ! is_unsatisfiable( cnf3 )
				)
		{ std::cout << "Hello World!" << std::endl; }
		return 0;
	}

}
#endif //GENTZEN_SYSTEM_EXAMPLE
