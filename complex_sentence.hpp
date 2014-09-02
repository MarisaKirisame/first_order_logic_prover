#ifndef FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#include "atomic_sentence.hpp"
#include "function.hpp"
#include "predicate.hpp"
#include <boost/variant.hpp>
namespace first_order_logic
{
	struct complex_sentence
	{
		enum class type { logical_and, logical_not, logical_or, all, some, atomic };
		struct internal
		{
			type cs_type;
			std::vector< boost::variant< boost::recursive_wrapper< complex_sentence >, atomic_sentence, term > > arguments;
			template< typename T >
			internal( type t, const T & r ) : cs_type( t ), arguments( r.begin( ), r.end( ) ) { }
			internal( const atomic_sentence & as ) : cs_type( type::atomic ), arguments( { as } ) { }
			template< typename ... T >
			internal( type, const T & ... ) { }
		};
		std::shared_ptr< internal > data;
		const internal * operator ->( ) const { return data.get( ); }
		const internal & operator *( ) const { return * data; }
		template< typename T >
		complex_sentence( type t, const T & r ) : data( new internal( t, r ) ) { }
		template< typename T >
		complex_sentence( type t, std::initializer_list< T > r ) : data( new internal( t, r ) ) { }
		template< typename ... T >
		complex_sentence( type t, const T & ... a ) : data( new internal( t, a ... ) ) { }
		complex_sentence( const atomic_sentence & as ) : data( new internal( as ) ) { }
		explicit operator std::string( ) const { throw; }
		bool is_quantifier( ) const { return data->cs_type == type::all || data->cs_type == type::some; }
		complex_sentence rebound( const term & old_term, const term & new_term ) const { throw old_term; throw new_term; }
		complex_sentence( const term & t ) { throw t; }
		std::set< function > functions( ) const { throw; }
		std::set< predicate > predicates( ) const { throw; }
		std::set< term > free_variables( ) const { throw; }
		std::set< term > constants( ) const { throw; }
		bool have_equal( ) const { throw; }
		std::shared_ptr< proof_tree > pt;
		bool operator < ( const complex_sentence & comp ) const { throw comp; }
		complex_sentence( ) { }
	};
}
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
