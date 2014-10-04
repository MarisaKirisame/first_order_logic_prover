#ifndef SENTENCE_HELPER_HPP
#define SENTENCE_HELPER_HPP
#include <type_traits>
#include "TMP.hpp"
namespace first_order_logic
{
	template< typename T >
	struct sentence;
	struct atomic_sentence;
	enum class sentence_type { logical_and = 0, logical_or = 1, logical_not = 2, all = 3, some = 4, pass = 5 };
	typedef
	sentence
	<
		vector
		<
			set_c
			<
				sentence_type,
				sentence_type::logical_and,
				sentence_type::logical_or,
				sentence_type::logical_not,
				sentence_type::some,
				sentence_type::all
			>
		>
	> free_sentence;
	template< typename T1, typename T2 >
	struct sentence_common;
	template< typename T >
	struct sentence_common< T, T > { typedef T type; };
	template< typename T >
	struct sentence_common< sentence< T >, sentence< T > > { typedef sentence< T > type; };
	template< typename T >
	struct sentence_common< sentence< T >, atomic_sentence > { typedef sentence< T > type; };
	template< typename T >
	struct sentence_common< atomic_sentence, sentence< T > > { typedef sentence< T > type; };
	template< typename T1, typename T2 >
	struct sentence_common< sentence< T1 >, sentence< T2 > >
	{
		typedef typename
		std::conditional
		<
			std::is_convertible< sentence< T1 >, sentence< T2 > >::value,
			sentence< T2 >,
			typename
			std::conditional
			<
				std::is_convertible< sentence< T2 >, sentence< T1 > >::value,
				sentence< T1 >,
				free_sentence
			>::type
		>::type type;
	};
	template< sentence_type st, typename T >
	struct add_sentence;
	template< sentence_type st >
	struct add_sentence< st, atomic_sentence >
	{ typedef sentence< vector< set_c< sentence_type, st > > > type; };
	template< sentence_type st, typename T >
	struct add_sentence< st, sentence< T > >
	{
		typedef typename
		std::conditional
		<
			front< T >::type::have( st ),
			sentence< T >,
			sentence< typename push_front< T, set_c< sentence_type, st > >::type >
		>::type type;
	};
}
#endif // SENTENCE_HELPER_HPP
