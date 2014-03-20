#ifndef GENTZEN_SYSTEM_VALUE_LESS
#define GENTZEN_SYSTEM_VALUE_LESS
#include <memory>
namespace gentzen_system
{
	template< typename t >
	struct value_less;

	template< typename t >
	struct value_less< std::shared_ptr< t > >
	{
		bool operator ( )( const std::shared_ptr< t > & lhs, const std::shared_ptr< t > & rhs ) const { return * lhs < * rhs; }
	};
}
#endif //GENTZEN_SYSTEM_VALUE_LESS
