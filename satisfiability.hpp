#ifndef FIRST_ORDER_LOGIC_SATISFIABILITY_HPP
#define FIRST_ORDER_LOGIC_SATISFIABILITY_HPP
#include <experimental/optional>
namespace first_order_logic
{
    enum class satisfiability { satisfiable, unsatisfiable };
    enum class validity { valid, invalid };
    template< typename OS >
    OS & operator << ( OS & os, satisfiability s )
    { return os << (s == satisfiability::satisfiable ? "satisfiable" : "unsatisfiable"); }
    template< typename OS >
    OS & operator << ( OS & os, validity s )
    { return os << (s == validity::valid ? "valid" : "invalid"); }
    std::experimental::optional< bool > is_satisfiable( satisfiability s ) { return s == satisfiability::satisfiable; }
    std::experimental::optional< bool > is_satisfiable( validity s )
    { return s == validity::valid ? std::experimental::optional< bool >( true ) : std::experimental::optional< bool >( ); }
    std::experimental::optional< bool > is_valid( validity s ) { return s == validity::valid; }
    std::experimental::optional< bool > is_valid( satisfiability s )
    { return s == satisfiability::satisfiable ? std::experimental::optional< bool >( ) : std::experimental::optional< bool >( false ); }
}
#endif //FIRST_ORDER_LOGIC_SATISFIABILITY_HPP
