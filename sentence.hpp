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
		RET type_restore( const ACTORS & ... t ) const
		{
			return type_restore_inner< RET >(
				extract< and_actor_helper >(
					t ...,
					make_and_actor(
						std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
				extract< or_actor_helper >(
					t ...,
					make_or_actor(
						std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
				extract< not_actor_helper >(
					t ...,
					make_not_actor(
						std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
				extract< all_actor_helper >(
					t ...,
					make_all_actor(
						std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
				extract< some_actor_helper >(
					t ...,
					make_some_actor(
						std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
				extract< atomic_actor_helper >(
					t ...,
					make_atomic_actor(
						std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ) );
		}
		template< typename RET, typename T1, typename T2, typename T3, typename T4, typename T5, typename T6 >
		RET type_restore_inner(
			const and_actor< T1 > & and_func,
			const or_actor< T2 > & or_func,
			const not_actor< T3 > & not_func,
			const all_actor< T4 > & all_func,
			const some_actor< T5 > & some_func,
			const atomic_actor< T6 > & atomic_func ) const
		{
			switch ( (*this)->type )
			{
				case sentence_type::logical_and:
					return and_func(
						boost::get< sentence< T > >( (*this)->arguments[0] ),
						boost::get< sentence< T > >( (*this)->arguments[1] ) );
				case sentence_type::logical_not:
					return not_func( boost::get< sentence< T > >( (*this)->arguments[0] ) );
				case sentence_type::logical_or:
					return or_func(
						boost::get< sentence< T > >( (*this)->arguments[0] ),
						boost::get< sentence< T > >( (*this)->arguments[1] ) );
				case sentence_type::all:
					return all_func(
						variable( (*this)->name ),
						boost::get< sentence< T > >( (*this)->arguments[0] ) );
				case sentence_type::some:
					return some_func(
						variable( (*this)->name ),
						boost::get< sentence< T > >( (*this)->arguments[0] ) );
				case sentence_type::pass:
					return misc::make_expansion(
								[&]( const atomic_sentence & as ){ return atomic_func( as ); },
								[&]( const next & n )
								{
									return n.template type_restore< RET >
											(
												and_func,
												or_func,
												not_func,
												all_func,
												some_func,
												atomic_func,
												error< RET >( )
											);
								} )
							( boost::get< next >( (*this)->arguments[0] ) );
			}
			throw std::invalid_argument( "unknown enum sentence_type" );
		}
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
		sentence< T > standardize_bound_variable( ) const
		{
			std::set< std::string > term_map;
			cv( make_function_output_iterator(
					[&]( const term & t )
					{
						assert( t->term_type == term::type::constant || t->term_type == term::type::variable );
						term_map.insert( t->name );
					} ) );
			return standardize_bound_variable( term_map );
		}
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
						std::is_convertible< ARG, sentence< TO > >::value
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
						! std::is_same< decltype( make_all( std::declval< variable >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value ||
						! std::is_convertible< ARG, sentence< TO > >::value
					>,
				typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
			>
			sentence< TO > operator ( )( const variable &, const ARG & ) const { throw; }
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
						std::is_convertible< ARG, sentence< TO > >::value
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
						! std::is_same< decltype( make_some( std::declval< variable >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value ||
						! std::is_convertible< ARG, sentence< TO > >::value
					>,
				typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
			>
			sentence< TO > operator ( )( const variable &, const ARG & ) const { throw; }
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
						std::is_convertible< ARG, sentence< TO > >::value
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
						! std::is_same< decltype( make_and( std::declval< sentence< TO > >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value ||
						! std::is_convertible< ARG, sentence< TO > >::value
					>,
				typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
			>
			sentence< TO > operator ( )( const ARG &, const ARG & ) const { throw; }
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
						std::is_convertible< ARG, sentence< TO > >::value
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
						! std::is_same< decltype( make_or( std::declval< sentence< TO > >( ), std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value ||
						! std::is_convertible< ARG, sentence< TO > >::value
					>,
				typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
			>
			sentence< TO > operator ( )( const ARG &, const ARG & ) const { throw; }
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
						std::is_convertible< ARG, sentence< TO > >::value
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
						! std::is_same< decltype( make_not( std::declval< sentence< TO > >( ) ) ), sentence< TO > >::value ||
						! std::is_convertible< ARG, sentence< TO > >::value
					>,
				typename = std::enable_if_t< std::is_same< ARG, ARG >::value >
			>
			sentence< TO > operator ( )( const ARG & ) const { throw; }
		};
		template< typename TO >
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
}
#include "implementation/sentence.hpp"
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
