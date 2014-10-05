#ifndef FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "sentence.hpp"
#include "atomic_sentence.hpp"
#include "term.hpp"
#include "variable.hpp"
#include "forward/first_order_logic.hpp"
#include "sentence_helper.hpp"
namespace first_order_logic
{
	inline term make_function( const std::string & s, const std::vector< term > & t )
	{ return term( term::type::function, s, t ); }

	inline term make_constant( const std::string & s )
	{ return term( constant( s ) ); }

	inline term make_variable( const std::string & s )
	{ return term( variable( s ) ); }

	inline atomic_sentence make_predicate( const std::string & s, const std::vector< term > & t )
	{ return atomic_sentence( atomic_sentence::type::predicate, s, t ); }

	inline atomic_sentence make_propositional_letter( const std::string & s )
	{ return atomic_sentence( atomic_sentence::type::propositional_letter, s ); }

	template< typename T >
	typename add_sentence_front< T, set_c< sentence_type, sentence_type::logical_not > >::type
	make_not( const T & s )
	{
		return typename
				add_sentence_front
				<
					T,
					set_c< sentence_type, sentence_type::logical_not >
				>::type( sentence_type::logical_not, { s } );
	}

	template< typename T1, typename T2 >
	typename add_sentence_front
	<
		typename sentence_common< T1, T2 >::type,
		set_c< sentence_type, sentence_type::logical_and >
	>::type
	make_and( const T1 & l, const T2 & r )
	{
		return
				typename add_sentence_front
				<
					typename sentence_common< T1, T2 >::type,
					set_c< sentence_type, sentence_type::logical_and >
				>::type
				(
					sentence_type::logical_and,
					{
						static_cast< typename sentence_common< T1, T2 >::type >( l ),
						static_cast< typename sentence_common< T1, T2 >::type >( r )
					}
				);
	}

	template< typename T1, typename T2 >
	typename add_sentence_front
	<
		typename sentence_common< T1, T2 >::type,
		set_c< sentence_type, sentence_type::logical_or >
	>::type
	make_or( const T1 & l, const T2 & r )
	{
		return
				typename add_sentence_front
				<
					typename sentence_common< T1, T2 >::type,
					set_c< sentence_type, sentence_type::logical_or >
				>::type
				(
					sentence_type::logical_or,
					{
						static_cast< typename sentence_common< T1, T2 >::type >( l ),
						static_cast< typename sentence_common< T1, T2 >::type >( r )
					}
				);
	}

	template< typename T >
	typename add_sentence_front< T, set_c< sentence_type, sentence_type::all > >::type
	make_all( const variable & l, const T & s )
	{
		return typename add_sentence_front< T, set_c< sentence_type, sentence_type::all > >::type(
					sentence_type::all, l, s );
	}

	template< typename T >
	typename add_sentence_front< T, set_c< sentence_type, sentence_type::some > >::type
	make_some( const variable & l, const T & s )
	{
		return typename add_sentence_front< T, set_c< sentence_type, sentence_type::some > >::type(
					sentence_type::some, l, s );
	}

	atomic_sentence make_equal( const term & l, const term & r )
	{ return atomic_sentence( atomic_sentence::type::equal, { l, r } ); }

}
#endif //FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
