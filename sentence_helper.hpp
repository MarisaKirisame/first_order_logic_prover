#ifndef SENTENCE_HELPER_HPP
#define SENTENCE_HELPER_HPP
#include <type_traits>
#include "TMP.hpp"
namespace first_order_logic
{
	template< typename T >
	struct sentence;
	template< typename T >
	struct sen2vec;
	template< typename T >
	struct sen2vec< sentence< T > > { typedef T type; };
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
	/*template< typename T1, typename T2 >
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
	};*/
	template< typename T, typename S >
	struct add_sentence_front;
	template< typename ... T >
	struct add_sentence_front< atomic_sentence, set< T ... > >
	{ typedef sentence< vector< set< T ... > > > type; };
	template< typename ... ARG, typename T >
	struct add_sentence_front< sentence< T >, set< ARG ... > >
	{
		typedef typename
		std::conditional
		<
			have< typename front< T >::type, set< ARG ... > >::value,
			sentence< T >,
			sentence< typename push_front< T, set< ARG ... > >::type >
		>::type type;
	};
	template< typename T, typename S >
	struct add_sentence_back;
	template< typename ... T >
	struct add_sentence_back< atomic_sentence, set< T ... > >
	{ typedef sentence< vector< set< T ... > > > type; };
	template< typename ... ARG, typename T >
	struct add_sentence_back< sentence< T >, set< ARG ... > >
	{
		typedef typename
		std::conditional
		<
			have< typename back< T >::type, set< ARG ... > >::value,
			sentence< T >,
			sentence< typename push_back< T, set< ARG ... > >::type >
		>::type type;
	};
	template< typename T, typename S >
	struct remove_operator;
	template< typename S >
	struct remove_operator< atomic_sentence, S > { typedef atomic_sentence type; };
	template< typename F, typename S >
	struct remove_operator< sentence< vector< F > >, S >
	{ typedef sentence< vector< typename remove< F, S >::type > > type; };
	template< typename F, typename ... T, typename S >
	struct remove_operator< sentence< vector< F, T ... > >, S >
	{
		typedef typename remove_operator< sentence< vector< F > >, S >::type top;
		typedef typename remove_operator< sentence< vector< T ... > >, S >::type down;
		typedef
		sentence
		<
			typename push_front
			<
				typename sen2vec< down >::type,
				typename back< typename sen2vec< top >::type >::type
			>::type
		> type;
	};
	template< typename T, typename S >
	struct move_operator_out
	{
		typedef typename
		add_sentence_front< typename remove_operator< T, S >::type, S >::type type;
	};
	template< typename T, typename S >
	struct move_operator_in
	{
		typedef typename
		add_sentence_back< typename remove_operator< T, S >::type, S >::type type;
	};
	template< typename >
	struct error_typename;
	struct no_such_sentence;
}
#endif // SENTENCE_HELPER_HPP
