#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "term.hpp"
namespace theorem_prover
{
	namespace first_order_logic
	{
		std::shared_ptr< term > make_function( const std::string & s, const std::vector< std::shared_ptr< term > > & t )
		{ return std::shared_ptr< term >( new term( s, t ) ); }

		std::shared_ptr< term > make_predicate( const std::string & s, const std::vector< std::shared_ptr< term > > & t )
		{ return std::shared_ptr< term >( new term( s, t ) ); }

		std::shared_ptr< term > make_constant( const std::string & s )
		{ return std::shared_ptr< term >( new term( std::string( "constant" ), { std::shared_ptr< term >( new term( s, { } ) ) } ) ); }

		std::shared_ptr< term > make_not( const std::shared_ptr< term > & s )
		{ return std::shared_ptr< term >( new term( std::string( "not" ), { s } ) ); }

		std::shared_ptr< term > make_and( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
		{ return std::shared_ptr< term >( new term( std::string( "and" ), { l, r } ) ); }

		std::shared_ptr< term > make_or( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
		{ return std::shared_ptr< term >( new term( std::string( "or" ), { l, r } ) ); }

		std::shared_ptr< term > make_imply( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
		{ return make_or( make_not( l ), r ); }

		std::shared_ptr< term > make_all( const std::string & l, const std::shared_ptr< term > & r )
		{ return std::shared_ptr< term >( new term( std::string( "all" ), { make_variable( l ), r } ) ); }

		std::shared_ptr< term > make_variable( const std::string & s )
		{ return std::shared_ptr< term >( new term( std::string( "variable" ), { std::shared_ptr< term >( new term( s, { } ) ) } ) ); }

		std::shared_ptr< term > make_some( const std::string & l, const std::shared_ptr< term > & r )
		{ return std::shared_ptr< term >( new term( std::string( "some" ), { make_variable( l ), r } ) ); }

		std::shared_ptr< term > make_equal( const std::shared_ptr< term > & l, const std::shared_ptr< term > & r )
		{ return std::shared_ptr< term >( new term( std::string( "equal" ), { l, r } ) ); }
	}
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
