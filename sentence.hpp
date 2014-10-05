#ifndef FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#include <type_traits>
#include "function.hpp"
#include "predicate.hpp"
#include "term.hpp"
#include <boost/variant.hpp>
#include "proof_tree.hpp"
#include "function_output_iterator.hpp"
#include "constant.hpp"
#include <boost/iterator/transform_iterator.hpp>
#include "named_parameter.hpp"
#include "forward/first_order_logic.hpp"
#include "sentence_helper.hpp"
#include "TMP.hpp"
#include "../misc/expansion.hpp"
namespace first_order_logic
{
	DEFINE_ACTOR(and);
	DEFINE_ACTOR(or);
	DEFINE_ACTOR(not);
	DEFINE_ACTOR(all);
	DEFINE_ACTOR(some);
	DEFINE_ACTOR(atomic);
	struct substitution;
	template< typename T >
	struct sentence
	{
		typedef typename front< T >::type current_set;
		typedef typename pop_front< T >::type next_vec;
		typedef typename
		std::conditional
		<
			empty< next_vec >::value,
			atomic_sentence,
			sentence< next_vec >
		>::type next;
		struct internal
		{
			sentence_type type;
			std::string name;
			mutable std::string cache;
			std::vector< boost::variant< boost::recursive_wrapper< sentence< T > >, next > > arguments;
			internal( sentence_type st, const sentence< T > & r ) :
				type( st ), arguments( { r } ) { }
			internal( sentence_type st, const next & r ) :
				type( st ), arguments( { r } ) { }
			internal( sentence_type st, const std::initializer_list< next > & r ) :
				type( st ), arguments( r.begin( ), r.end( ) ) { }
			internal( sentence_type st, const std::initializer_list< sentence< T > > & r ) :
				type( st ), arguments( r.begin( ), r.end( ) ) { }
			internal( sentence_type st, const std::string & name ) :
				type( st ), name( name ) { }
			internal( sentence_type ty, const variable & l, const sentence< T > & r ) :
				type( ty ), name( l.name ), arguments( { r } ) { }
		};
		std::shared_ptr< internal > data;
		internal * operator ->( ) const { return data.get( ); }
		internal & operator * ( ) const { return * data; }
		template< typename RET, typename ... ACTORS >
		RET type_restore_full( const ACTORS & ... t ) const
		{
			static_assert( std::tuple_size< std::tuple< ACTORS ... > >::value == 6, "should have six arguments" );
			return type_restore< RET >( t ..., error< RET >( ) );
		}
		template< typename RET, typename ... ACTORS >
		RET type_restore( const ACTORS & ... t ) const;
		template< typename RET, typename T1, typename T2, typename T3, typename T4, typename T5, typename T6 >
		RET type_restore_inner(
			const and_actor< T1 > & and_func,
			const or_actor< T2 > & or_func,
			const not_actor< T3 > & not_func,
			const all_actor< T4 > & all_func,
			const some_actor< T5 > & some_func,
			const atomic_actor< T6 > & atomic_func ) const;
		explicit operator std::string( ) const;
		sentence( sentence_type ty, const std::initializer_list< next > & il ) :
			data( new internal( ty, il ) ) { }
		sentence( sentence_type ty, const std::initializer_list< sentence< T > > & il ) :
			data( new internal( ty, il ) ) { }
		sentence( sentence_type ty, const next & il ) :
			data( new internal( ty, il ) ) { }
		sentence( sentence_type ty, const variable & l, const sentence< T > & r ) :
			data( new internal( ty, l, r ) ) { }
		sentence( ) { }
		sentence( const atomic_sentence & as ) : sentence( sentence_type::pass, next( as ) ) { }
		bool operator == ( const sentence< T > & comp ) const { return !( (*this) < comp || comp < (*this) ); }
		bool operator != ( const sentence< T > & comp ) const { return ! ( (*this) == comp ); }
		size_t length( ) const;
		template< typename OUTITER >
		OUTITER functions( OUTITER result ) const;
		template< typename OUTITER >
		OUTITER predicates( OUTITER result ) const;
		template< typename OUTITER >
		OUTITER variables( OUTITER result ) const;
		template< typename OUTITER >
		OUTITER bounded_variables( OUTITER result ) const;
		template< typename OUTITER >
		OUTITER free_variables( OUTITER result ) const;
		bool have_equal( ) const;
		template< typename OUTITER >
		OUTITER constants( OUTITER result ) const;
		template< typename OUTITER >
		OUTITER cv( OUTITER result ) const
		{
			free_variables( constants( make_function_output_iterator(
										[&]( const auto & v ) { *result = term( v ); ++result; } ) ) );
			return result;
		}
		bool operator < ( const sentence< T > & comp ) const
		{
			if ( length( ) < comp.length( ) ) { return true; }
			if ( length( ) > comp.length( ) ) { return false; }
			return static_cast< std::string >( * this ) < static_cast< std::string >( comp );
		}
		bool have_quantifier( ) const;
		bool is_in_prenex_form( ) const;
		sentence< T > standardize_bound_variable( ) const;
		sentence< T > standardize_bound_variable( std::set< std::string > & term_map ) const;
		sentence< T > move_quantifier_out( ) const;
		sentence< T > skolemization_remove_existential( std::set< variable > & previous_quantifier ) const;
		sentence< T > skolemization_remove_universal( std::set< variable > & previous_quantifier ) const;
		sentence< T > skolemization_remove_existential( ) const;
		sentence< T > skolemization_remove_universal( ) const;
		sentence< T > drop_existential( ) const;
		sentence< T > drop_universal( ) const;
		sentence< T > rectify( ) const;
		sentence< T > rectify(
					std::set< variable > & used_quantifier,
					const std::set< variable > & free_variable,
					std::set< std::string > & used_name ) const;
		template< typename OUTITER >
		OUTITER used_name( OUTITER result ) const;
		explicit operator bool ( ) const { return data.get( ) != nullptr; }
		void swap( sentence< T > & sen ) { data.swap( sen.data ); }
		sentence< T > restore_quantifier_existential( ) const;
		sentence< T > restore_quantifier_universal( ) const;
		template< typename OSTREAM >
		friend OSTREAM & operator << ( OSTREAM & os, const sentence< T > & sen )
		{ return os << static_cast< std::string >( sen ); }
		template
		<
			typename TO,
			typename =
				std::enable_if_t
				<
					! std::is_same< decltype( and_converter< TO >( )( std::declval< sentence< T > >( ), std::declval< sentence< T > >( ) ) ), boost::mpl::false_ >::value &&
					! std::is_same< decltype( or_converter< TO >( )( std::declval< sentence< T > >( ), std::declval< sentence< T > >( ) ) ), boost::mpl::false_ >::value &&
					! std::is_same< decltype( not_converter< TO >( )( std::declval< sentence< T > >( ) ) ), boost::mpl::false_ >::value &&
					! std::is_same< decltype( all_converter< TO >( )( std::declval< variable >( ), std::declval< sentence< T > >( ) ) ), boost::mpl::false_ >::value &&
					! std::is_same< decltype( some_converter< TO >( )( std::declval< variable >( ), std::declval< sentence< T > >( ) ) ), boost::mpl::false_ >::value
				>
		>
		operator sentence< TO >( ) const
		{
			switch ( (*this)->type )
			{
				case sentence_type::logical_and:
					return and_converter< TO >( )(
						boost::get< sentence< T > >( (*this)->arguments[0] ),
						boost::get< sentence< T > >( (*this)->arguments[1] ) );
				case sentence_type::logical_not:
					return not_converter< TO >( )( boost::get< sentence< T > >( (*this)->arguments[0] ) );
				case sentence_type::logical_or:
					return or_converter< TO >( )(
						boost::get< sentence< T > >( (*this)->arguments[0] ),
						boost::get< sentence< T > >( (*this)->arguments[1] ) );
				case sentence_type::all:
					return all_converter< TO >( )(
						variable( (*this)->name ),
						boost::get< sentence< T > >( (*this)->arguments[0] ) );
				case sentence_type::some:
					return some_converter< TO >( )(
						variable( (*this)->name ),
						boost::get< sentence< T > >( (*this)->arguments[0] ) );
				case sentence_type::pass:
					return sentence< TO >( boost::get< next >( (*this)->arguments[0] ) );
			}
			throw std::invalid_argument( "unknown enum sentence_type" );
		}
	};
	static_assert( std::is_convertible< sentence< vector< set_c< sentence_type, sentence_type::logical_not > > >, const free_sentence & >::value, "must be convertible to free sentence" );
	static_assert( ! std::is_convertible< free_sentence, const sentence< vector< set_c< sentence_type, sentence_type::logical_not > > > & >::value, "must be convertible to free sentence" );
}
#include "implementation/sentence.hpp"
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
