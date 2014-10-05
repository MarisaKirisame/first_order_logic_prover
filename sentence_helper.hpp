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
	template< typename TO >
	struct all_converter
	{
		template
		<
			typename ARG,
			typename = std::enable_if_t< std::is_convertible< ARG, typename sentence< TO >::next >::value >
		>
		sentence< TO > operator ( )( const variable & v, const ARG & t ) const
		{ return sentence< TO >( sentence_type::all, v, typename sentence< TO >::next( t ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< std::is_same< decltype( make_all( std::declval< variable >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >
		>
		sentence< TO > operator ( )( const variable & v, const ARG & t ) const { return make_all( v, t ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_all( std::declval< variable >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					std::is_same< decltype( make_all( std::declval< variable >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>
		>
		sentence< TO > operator ( )( const variable & v, const ARG & a ) const { return make_all( v, sentence< TO >( a ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_all( std::declval< variable >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					! std::is_same< decltype( make_all( std::declval< variable >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value
					&& std::is_same< ARG, ARG >::value
				>,
			typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
		>
		boost::mpl::false_ operator ( )( const variable &, const ARG & ) const { throw; }
	};
	template< typename TO >
	struct some_converter
	{
		template
		<
			typename ARG,
			typename = std::enable_if_t< std::is_convertible< ARG, typename sentence< TO >::next >::value >
		>
		sentence< TO > operator ( )( const variable & v, const ARG & t ) const
		{ return sentence< TO >( sentence_type::some, v, typename sentence< TO >::next( t ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< std::is_same< decltype( make_some( std::declval< variable >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >
		>
		sentence< TO > operator ( )( const variable & v, const ARG & t ) const { return make_some( v, t ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_some( std::declval< variable >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					std::is_same< decltype( make_some( std::declval< variable >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>
		>
		sentence< TO > operator ( )( const variable & v, const ARG & a ) const { return make_some( v, sentence< TO >( a ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_some( std::declval< variable >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					! std::is_same< decltype( make_some( std::declval< variable >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>,
			typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
		>
		boost::mpl::false_ operator ( )( const variable &, const ARG & ) const { throw; }
	};
	template< typename TO >
	struct and_converter
	{
		template
		<
			typename ARG,
			typename = std::enable_if_t< std::is_convertible< ARG, typename sentence< TO >::next >::value >
		>
		sentence< TO > operator ( )( const ARG & l, const ARG & r ) const
		{ return sentence< TO >( sentence_type::logical_and, { typename sentence< TO >::next( l ), typename sentence< TO >::next( r ) } ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< std::is_same< decltype( make_and( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >
		>
		sentence< TO > operator ( )( const ARG & l, const ARG & r ) const { return make_and( l, r ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_and( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					std::is_same< decltype( make_and( std::declval< sentence< TO > >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>
		>
		sentence< TO > operator ( )( const ARG & l, const ARG & r ) const { return make_and( sentence< TO >( l ), sentence< TO >( r ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_and( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					! std::is_same< decltype( make_and( std::declval< sentence< TO > >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>,
			typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
		>
		boost::mpl::false_ operator ( )( const ARG &, const ARG & ) const { throw; }
	};
	template< typename TO >
	struct or_converter
	{
		template
		<
			typename ARG,
			typename = std::enable_if_t< std::is_convertible< ARG, typename sentence< TO >::next >::value >
		>
		sentence< TO > operator ( )( const ARG & l, const ARG & r ) const
		{ return sentence< TO >( sentence_type::logical_or, { typename sentence< TO >::next( l ), typename sentence< TO >::next( r ) } ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< std::is_same< decltype( make_or( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >
		>
		sentence< TO > operator ( )( const ARG & l, const ARG & r ) const { return make_or( l, r ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_or( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					std::is_same< decltype( make_or( std::declval< sentence< TO > >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>
		>
		sentence< TO > operator ( )( const ARG & l, const ARG & r ) const { return make_or( sentence< TO >( l ), sentence< TO >( r ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_or( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					! std::is_same< decltype( make_or( std::declval< sentence< TO > >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>,
			typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
		>
		boost::mpl::false_ operator ( )( const ARG &, const ARG & ) const { throw; }
	};
	template< typename TO >
	struct not_converter
	{
		template
		<
			typename ARG,
			typename = std::enable_if_t< std::is_convertible< ARG, typename sentence< TO >::next >::value >
		>
		sentence< TO > operator ( )( const ARG & l ) const
		{ return sentence< TO >( sentence_type::logical_not, { typename sentence< TO >::next( l ) } ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< std::is_same< decltype( make_not( std::declval< ARG >( ), std::declval< ARG >( ) ) ), sentence< TO > >::value >
		>
		sentence< TO > operator ( )( const ARG & l ) const { return make_not( l ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_not( std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					std::is_same< decltype( make_not( std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>
		>
		sentence< TO > operator ( )( const ARG & l ) const { return make_not( sentence< TO >( l ) ); }
		template
		<
			typename ARG,
			typename = std::enable_if_t< ! std::is_convertible< ARG, typename sentence< TO >::next >::value, bool >,
			typename = std::enable_if_t< ! std::is_same< decltype( make_not( std::declval< ARG >( ) ) ), sentence< TO > >::value >,
			typename =
				std::enable_if_t
				<
					! std::is_same< decltype( make_not( std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value &&
					std::is_same< ARG, ARG >::value
				>,
			typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
		>
		boost::mpl::false_ operator ( )( const ARG & ) const { throw; }
	};
}
#endif // SENTENCE_HELPER_HPP
