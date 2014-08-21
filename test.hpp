#ifndef THEOREM_PROVER_EXAMPLE
#define THEOREM_PROVER_EXAMPLE
#define BOOST_TEST_MAIN
#define BOOST_TEST_DYN_LINK
#include <boost/test/unit_test.hpp>
#include "first_order_logic.hpp"
#include "praser.hpp"
namespace first_order_logic
{
	BOOST_AUTO_TEST_CASE( first_order_logic_test )
	{
		auto fol = make_imply(
								 make_all( "x", make_predicate( "F", { make_variable( "x" ) } ) ),
								 make_all( "x", make_predicate( "F", { make_function( "f", { make_variable( "x" ) } ) } ) ) );
		auto fol2 = make_imply(
								make_some(
									"x",
									make_imply(
										make_variable( "p" ),
										make_function( "Q", { make_variable( "x" ) } )
										) ),
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
		BOOST_CHECK( fol->is_valid( ) );
		BOOST_CHECK( fol2->is_valid( ) );
		BOOST_CHECK( fol3->is_valid( ) );
		BOOST_CHECK( fol4->is_valid( ) );
	}
}
#endif //THEOREM_PROVER_EXAMPLE
