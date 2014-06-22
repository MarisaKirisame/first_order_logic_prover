#ifndef THEOREM_PROVER_EXAMPLE
#define THEOREM_PROVER_EXAMPLE
#include "propositional_logic/proposition.hpp"
#include "first_order_logic/first_order_logic.hpp"
#include "propositional_logic/resolution_method.hpp"
#include "first_order_logic/praser.hpp"
namespace theorem_prover
{
	void propositional_logic_test( )
	{
		using namespace propositional_logic;
		std::shared_ptr< proposition > A( new proposition( "A" ) );
		std::shared_ptr< proposition > B( new proposition( "B" ) );
		std::shared_ptr< proposition > C( new proposition( "C" ) );
		std::shared_ptr< proposition > not_a( proposition::make_not( A ) );
		std::shared_ptr< proposition > valid_prop( proposition::make_or( A, not_a ) );
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
		assert(
					res1 == satisfiable &&
					res2 == valid &&
					res3 == unsatisfiable &&
					associativity_law_prop->get_satisfiability( ) == valid &&
					valid_prop2->get_satisfiability( ) == valid &&
					is_unsatisfiable( cnf ) && is_unsatisfiable( cnf2 ) && ! is_unsatisfiable( cnf3 ) );
	}

	void first_order_logic_test( )
	{
		using namespace first_order_logic;
		auto fol = make_or(
								 make_variable( "A" ),
								 make_not(
									 make_variable( "A" ) ) );
		auto fol2 = make_imply(
									make_some(
										"x",
										make_imply(
											make_variable( "p" ),
											make_function( "Q", { make_variable( "x" ) } )
											)
										),
									make_imply(
										make_variable( "p" ),
										make_some(
											"z",
											make_function( "Q", { make_variable( "z" ) } ) ) )
									);
		auto fol3 = make_imply(
									make_and(
										make_all(
											"x",
											make_function( "P", { make_variable( "x" ) } ) ),
										make_some(
											"y",
											make_function( "Q", { make_variable( "y" ) } ) ) ),
									make_and(
										make_function(
											"P",
											{ make_function( "F",  { make_variable( "v" ) } ) } ),
										make_some(
											"z",
											make_function( "Q", { make_variable( "z" ) } ) ) ) );
		auto fol4 = make_imply(
									make_and(
										make_function( "p", { make_variable( "x" ) } ),
											make_equal( make_function( "f", { make_variable( "x" ) } ), make_variable( "x" ) ) ),
									make_function( "p", { make_function( "f", { make_variable( "x" ) } ) } ) );
		assert( fol->is_valid( ) && fol2->is_valid( ) && fol3->is_valid( ) && fol4->is_valid( ) );
	}

	int example( )
	{
		std::string str = u8"∃a a=a";
		auto res = first_order_logic::prase( str );
		std::cout << res->is_valid( ) << std::endl;
		return 0;
	}

}
#endif //THEOREM_PROVER_EXAMPLE
