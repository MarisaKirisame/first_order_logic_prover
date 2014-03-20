#ifndef GENTZEN_SYSTEM_EXAMPLE
#define GENTZEN_SYSTEM_EXAMPLE
#include "proposition.hpp"
#include "first_order_logic.hpp"
#include "resolution_method.hpp"
namespace gentzen_system
{
	int example( )
	{
		std::shared_ptr< proposition > A( new proposition( "A" ) );//A
		std::shared_ptr< proposition > B( new proposition( "B" ) );//B
		std::shared_ptr< proposition > C( new proposition( "C" ) );//C
		std::shared_ptr< proposition > not_a( proposition::make_not( A ) );//!A
		std::shared_ptr< proposition > valid_prop( proposition::make_or( A, not_a ) );//A or ! A( valid )
		std::shared_ptr< proposition > unsatisfiable_prop( proposition::make_and( A, not_a ) );
		std::shared_ptr< proposition > associativity_law_prop(
					proposition::make_equal(
						proposition::make_or(
							proposition::make_or( A, B ),
							C ),
						proposition::make_or(
							proposition::make_or( B, C ),
							A ) ) );
		std::shared_ptr< proposition > valid_prop2( proposition::make_imply( A, proposition::make_imply( B, A ) ) );
		auto res1 = A->get_satisfiability( );
		auto res2 = valid_prop->get_satisfiability( );
		auto res3 = unsatisfiable_prop->get_satisfiability( );
		auto cnf = to_CNF( unsatisfiable_prop );
		auto cnf2 = to_CNF( proposition::make_not( associativity_law_prop ) );
		auto cnf3 = to_CNF( associativity_law_prop );
		auto fol = term::deduction_tree::make_or( term::deduction_tree::make_variable( "A" ), term::deduction_tree::make_not( term::deduction_tree::make_variable( "A" ) ) );
		if (
				res1 == satisfiable &&
				res2 == valid &&
				res3 == unsatisfiable &&
				associativity_law_prop->get_satisfiability( ) == valid &&
				valid_prop2->get_satisfiability( ) == valid &&
				is_unsatisfiable( cnf ) && is_unsatisfiable( cnf2 ) && ! is_unsatisfiable( cnf3 ) &&
				fol->is_valid( )
				)
		{ std::cout << "Hello World!" << std::endl; }
		return 0;
	}

}
#endif //GENTZEN_SYSTEM_EXAMPLE
