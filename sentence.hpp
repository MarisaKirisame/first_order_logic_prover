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
#include "converter.hpp"
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
		static_assert( is_vector< T >::value, "T should be vector" );
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
		template< typename ... ACTORS >
		struct full_type_restore
		{
			template< typename ACTOR, typename UNTESTED, typename PLACEHOLDER >
			struct have_operator_actor;
			template< typename UNTESTED, typename PLACEHOLDER >
			struct have_operator_actor< vector< >, UNTESTED, PLACEHOLDER > : std::false_type { };
			template< typename PLACEHOLDER >
			struct have_operator_actor< vector< >, set< >, PLACEHOLDER > : std::true_type { };
			template< typename V, typename PLACEHOLDER >
			struct have_operator_actor< V, set< >, PLACEHOLDER > : std::true_type { };
#define HAVE_OPERATOR_ACTOR_GENERATOR( actor_name, enum_name ) \
			template< typename F, typename ... R, typename S, typename PLACEHOLDER > \
			struct have_operator_actor< vector< actor_name, R ... >, S, PLACEHOLDER > : \
					have_operator_actor \
					< \
						vector< R ... >, \
						typename remove< S, set_c< sentence_type, enum_name > >::type, \
						PLACEHOLDER \
					> { }; \
			template< typename F, typename ... R, typename PLACEHOLDER > \
			struct have_operator_actor< vector< actor_name, R ... >, set< >, PLACEHOLDER > : std::true_type { }
			HAVE_OPERATOR_ACTOR_GENERATOR( all_actor< F >, sentence_type::all );
			HAVE_OPERATOR_ACTOR_GENERATOR( some_actor< F >, sentence_type::some );
			HAVE_OPERATOR_ACTOR_GENERATOR( and_actor< F >, sentence_type::logical_and );
			HAVE_OPERATOR_ACTOR_GENERATOR( not_actor< F >, sentence_type::logical_not );
			HAVE_OPERATOR_ACTOR_GENERATOR( or_actor< F >, sentence_type::logical_or );
			HAVE_OPERATOR_ACTOR_GENERATOR( atomic_actor< F >, sentence_type::pass );
#undef HAVE_OPERATOR_ACTOR_GENERATOR
			template< typename ... ACTOR >
			struct have_atomic_actor;
			template< typename PLACEHOLDER >
			struct have_atomic_actor< PLACEHOLDER > : std::false_type { };
			template< typename FIRST, typename ... REST >
			struct have_atomic_actor< FIRST, REST ... > : have_atomic_actor< REST ... > { };
			template< typename FIRST, typename ... REST >
			struct have_atomic_actor< atomic_actor< FIRST >, REST ... > : std::true_type { };
			template< typename SEN, typename ... ACTOR >
			struct recurse_predicate;
			template< typename ... ACTOR >
			struct recurse_predicate< atomic_sentence, ACTOR ... > : std::true_type { };
			template< typename SEN, typename ... ACTOR >
			struct recurse_predicate< sentence< SEN >, ACTOR ... > :
					sentence< SEN >::template full_type_restore< ACTOR ... > { };
			constexpr static bool value =
					have_operator_actor< vector< ACTORS ... >, current_set, void >::value &&
					have_atomic_actor< ACTORS ..., void >::value &&
					recurse_predicate< next, ACTORS ... >::value;
		};
		template< typename RET, typename ... ACTORS >
		RET type_restore_full( const ACTORS & ... t ) const
		{
			static_assert( full_type_restore< ACTORS ... >::value, "type missing" );
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
		typename
		move_operator_out
		<
			sentence< T >,
			set_c< sentence_type, sentence_type::all, sentence_type::some >
		>::type move_quantifier_out( ) const;
		typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
		skolemization_remove_existential( std::set< variable > & previous_quantifier ) const;
		typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
		skolemization_remove_universal( std::set< variable > & previous_quantifier ) const;
		typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
		skolemization_remove_existential( ) const;
		typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
		skolemization_remove_universal( ) const;
		typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
		drop_existential( ) const;
		typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
		drop_universal( ) const;
		sentence< T > rectify( ) const;
		sentence< T > rectify(
					std::set< variable > & used_quantifier,
					const std::set< variable > & free_variable,
					std::set< std::string > & used_name ) const;
		template< typename OUTITER >
		OUTITER used_name( OUTITER result ) const;
		explicit operator bool ( ) const { return data.get( ) != nullptr; }
		void swap( sentence< T > & sen ) { data.swap( sen.data ); }
		typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
		restore_quantifier_existential( ) const;
		typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
		restore_quantifier_universal( ) const;
		template< typename OSTREAM >
		friend OSTREAM & operator << ( OSTREAM & os, const sentence< T > & sen )
		{ return os << static_cast< std::string >( sen ); }
		template
		<
			typename TO,
			typename =
				std::enable_if_t
				<
					! std::is_same<
						decltype( and_converter< TO >( )( std::declval< sentence< T > >( ),
						std::declval< sentence< T > >( ) ) ), void >::value &&
					! std::is_same<
						decltype( or_converter< TO >( )( std::declval< sentence< T > >( ),
						std::declval< sentence< T > >( ) ) ), void >::value &&
					! std::is_same<
						decltype( not_converter< TO >( )( std::declval< sentence< T > >( ) ) ),
						void >::value &&
					! std::is_same<
						decltype( all_converter< TO >( )( std::declval< variable >( ), std::declval< sentence< T > >( ) ) ),
						void >::value &&
					! std::is_same<
						decltype( some_converter< TO >( )( std::declval< variable >( ), std::declval< sentence< T > >( ) ) ),
						void >::value
				>
		>
		operator sentence< TO >( ) const;
	};
	static_assert(
			std::is_convertible<
				sentence< vector< set_c< sentence_type, sentence_type::logical_not > > >,
				const free_sentence & >::value,
			"must be convertible to free sentence" );
	static_assert(
			! std::is_convertible<
				free_sentence,
				const sentence< vector< set_c< sentence_type, sentence_type::logical_not > > > & >::value,
			"must be convertible to free sentence" );
}
#include "implementation/sentence.hpp"
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
