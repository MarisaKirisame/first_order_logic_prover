#ifndef SENTENCE_HELPER_HPP
#define SENTENCE_HELPER_HPP
#include <type_traits>
#include "TMP.hpp"
namespace first_order_logic
{
	template< typename T >
	struct sentence;
	struct atomic_sentence;
	template< typename T >
	struct is_atomic_sentence : std::false_type { };
	template< >
	struct is_atomic_sentence< atomic_sentence > : std::true_type { };
	template< typename T >
	struct current_set;
	template< typename T >
	struct current_set< sentence< T > > { typedef typename front< T >::type type; };
	template< typename T >
	struct next_sentence_type;
	template< typename T >
	struct next_sentence_type< sentence< T > >
	{
		typedef typename pop_front< T >::type next_vec;
		typedef typename
		std::conditional
		<
			empty< next_vec >::value,
			atomic_sentence,
			sentence< next_vec >
		>::type type;
	};
	template< typename T >
	struct sen2vec;
	template< typename T >
	struct sen2vec< sentence< T > > { typedef T type; };
	struct atomic_sentence;
	enum class sentence_type { logical_and = 0, logical_or = 1, logical_not = 2, all = 3, some = 4, pass = 5 };
	template< typename OS >
	OS & operator << ( OS & os, const sentence_type & st )
	{
		return os <<
					( st == sentence_type::logical_and ? "and" :
					st == sentence_type::logical_or ? "or" :
					st == sentence_type::logical_not ? "not" :
					st == sentence_type::some ? "some" :
					st == sentence_type::all ? "all" :
					st == sentence_type::pass ? "pass" : std::to_string( static_cast< long >( st ) ) );
	}
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
	template< typename S >
	struct all_sentence_operator;
	template< >
	struct all_sentence_operator< atomic_sentence > { typedef set< > type; };
	template< typename S >
	struct all_sentence_operator< sentence< S > >
	{
		typedef typename
		join
		<
			typename current_set< sentence< S > >::type,
			typename all_sentence_operator< typename next_sentence_type< sentence< S > >::type >::type
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
		typedef typename
		back
		<
			typename sen2vec
			<
				typename remove_operator
				<
					sentence< vector< F > >,
					S
				>::type
			>::type
		>::type top;
		typedef typename sen2vec< typename remove_operator< sentence< vector< T ... > >, S >::type >::type down;
		typedef
		sentence
		<
			typename std::conditional
			<
				empty< top >::value,
				down,
				typename push_front< down, top >::type
			>::type
		> type;
	};
	template< typename T, typename S >
	struct move_operator_out
	{
		typedef typename
		add_sentence_front
		<
			typename remove_operator< T, S >::type,
			typename subset< S, typename all_sentence_operator< T >::type >::type
		>::type type;
	};
	template< typename T, typename S >
	struct move_operator_in
	{
		typedef typename
		add_sentence_back
		<
			typename remove_operator< T, S >::type,
			typename subset< S, typename all_sentence_operator< T >::type >::type
		>::type type;
	};
	template< typename >
	struct error_typename;
	struct no_such_sentence;
}
namespace std
{
	template< typename L, typename R >
	struct std::common_type< first_order_logic::sentence< L >, first_order_logic::sentence< R > >
	{
		template
		<
			bool = std::is_convertible< first_order_logic::sentence< L >, first_order_logic::sentence< R > >::value,
			bool = std::is_convertible< first_order_logic::sentence< R >, first_order_logic::sentence< L > >::value,
			typename PLACEHOLDER = void
		>
		struct inner;
		template< typename PLACEHOLDER >
		struct inner< true, false, PLACEHOLDER > { typedef first_order_logic::sentence< R > type; };
		template< typename PLACEHOLDER >
		struct inner< false, true, PLACEHOLDER > { typedef first_order_logic::sentence< L > type; };
		template< typename PLACEHOLDER >
		struct inner< false, false, PLACEHOLDER >
		{
			template< typename LL, typename RR >
			struct HELPER;
			template< typename LL, typename RR >
			struct HELPER
					<
						first_order_logic::sentence< first_order_logic::vector< LL > >,
						first_order_logic::sentence< first_order_logic::vector< RR > >
					>
			{
				typedef first_order_logic::sentence
				< first_order_logic::vector< typename first_order_logic::join< LL, RR >::type > >
				type;
			};
			template< typename ... LLL, typename LL, typename RR >
			struct HELPER
					<
						first_order_logic::sentence< first_order_logic::vector< LL, LLL ... > >,
						first_order_logic::sentence< first_order_logic::vector< RR > >
					>
			{
				typedef typename
				first_order_logic::add_sentence_back
				<
					first_order_logic::sentence
					< typename first_order_logic::pop_back< first_order_logic::vector< LL, LLL ... > >::type >,
					typename first_order_logic::join
					< typename first_order_logic::back< first_order_logic::vector< LL, LLL ... > >::type, RR >::type
				>::type type;
			};
			template< typename ... RRR, typename LL, typename RR >
			struct HELPER
			<
				first_order_logic::sentence< first_order_logic::vector< LL > >,
				first_order_logic::sentence< first_order_logic::vector< RR, RRR ... > >
			> :
				HELPER
				<
					first_order_logic::sentence< first_order_logic::vector< RR, RRR ... > >,
					first_order_logic::sentence< first_order_logic::vector< LL > >
				> { };
			template< typename ... LLL, typename ... RRR >
			struct HELPER
			<
				first_order_logic::sentence< first_order_logic::vector< LLL ... > >,
				first_order_logic::sentence< first_order_logic::vector< RRR ... > >
			>
			{
				typedef typename
				first_order_logic::add_sentence_back
				<
					typename common_type
					<
						first_order_logic::sentence
						< typename first_order_logic::pop_back< first_order_logic::vector< LLL ... > >::type >,
						first_order_logic::sentence
						< typename first_order_logic::pop_back< first_order_logic::vector< RRR ... > >::type >
					>::type,
					typename first_order_logic::join
					<
						typename first_order_logic::back< first_order_logic::vector< LLL ... > >::type,
						typename first_order_logic::back< first_order_logic::vector< RRR ... > >::type
					>::type
				>::type type;
			};
			typedef typename HELPER< first_order_logic::sentence< L >, first_order_logic::sentence< R > >::type type;
		};
		template< typename PLACEHOLDER >
		struct inner< true, true, PLACEHOLDER >
		{ typedef first_order_logic::sentence< L > type; };
		typedef typename inner< >::type type;
	};
}

#endif // SENTENCE_HELPER_HPP
