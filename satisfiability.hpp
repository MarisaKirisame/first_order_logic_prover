#ifndef SATISFIABILITY_HPP
#define SATISFIABILITY_HPP
#include <boost/optional/optional.hpp>
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
    boost::optional< bool > is_satisfiable( satisfiability s ) { return s == satisfiability::satisfiable; }
    boost::optional< bool > is_satisfiable( validity s )
    { return s == validity::valid ? boost::optional< bool >( true ) : boost::optional< bool >( ); }
    boost::optional< bool > is_valid( validity s ) { return s == validity::valid; }
    boost::optional< bool > is_valid( satisfiability s )
    { return s == satisfiability::satisfiable ? boost::optional< bool >( ) : boost::optional< bool >( false ); }
}
#endif // SATISFIABILITY_HPP
