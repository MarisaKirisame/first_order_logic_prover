#ifndef TMP_HPP
#define TMP_HPP
#include <type_traits>
namespace first_order_logic
{
	//I KNOW I CAN USE BOOST::MPL
	//AND I TRY BUT THE RESULT IS IMPOSSIBLE TO DEBUG
	//SO I WILL REINVENT THE WHEEL UNTIL I CAN READ
	template< typename T, T ... element > struct set_c;
	template< typename T > struct set_c< T >
	{ constexpr static bool have( T ) { return false; } };
	template< typename T, T f, T ... rest >
	struct set_c< T, f, rest ... >
	{
		constexpr static bool have( T st )
		{ return st == f || set_c< T, rest ... >::have( st ); }
	};
	template< typename ... T >
	struct vector;
	template< typename T > struct pop_front;
	template< typename F, typename ... R >
	struct pop_front< vector< F, R ... > > { typedef vector< R ... > type; };
	template< typename T > struct empty;
	template< typename F, typename ... R >
	struct empty< vector< F, R ... > > : std::false_type { };
	template< >
	struct empty< vector< > > : std::true_type { };
	template< typename T > struct front;
	template< typename F, typename ... R >
	struct front< vector< F, R ... > > { typedef F type; };
	template< typename T, typename ADD > struct push_front;
	template< typename ADD, typename ... R >
	struct push_front< vector< R ... >, ADD > { typedef vector< ADD, R ... > type; };
}
#endif // TMP_HPP
