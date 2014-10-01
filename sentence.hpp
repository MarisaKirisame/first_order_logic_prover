#ifndef FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#include "function.hpp"
#include "predicate.hpp"
#include "term.hpp"
#include <boost/variant.hpp>
#include "proof_tree.hpp"
#include <boost/mpl/bool.hpp>
#include "function_output_iterator.hpp"
#include "constant.hpp"
#include <boost/iterator/transform_iterator.hpp>
#include "named_parameter.hpp"
#include "atomic_sentence.hpp"
namespace first_order_logic
{
	DEFINE_ACTOR(and);
	DEFINE_ACTOR(or);
	DEFINE_ACTOR(not);
	DEFINE_ACTOR(all);
	DEFINE_ACTOR(some);
	DEFINE_ACTOR(atomic);
	struct substitution;
	struct sentence
	{
		enum class type { logical_and, logical_or, logical_not, all, some, atomic };
		struct internal
		{
			type sentence_type;
			std::string name;
			mutable std::string cache;
			std::vector< boost::variant< boost::recursive_wrapper< sentence >, atomic_sentence > > arguments;
			internal( type sentence_type, const atomic_sentence & r ) :
				sentence_type( sentence_type ), arguments( { r } ) { }
			template< typename T >
			internal( type sentence_type, const std::string & name, const T & r ) :
				sentence_type( sentence_type ), name( name ), arguments( r.begin( ), r.end( ) ) { }
			template< typename T >
			internal( type sentence_type, const T & r ) :
				sentence_type( sentence_type ), arguments( r.begin( ), r.end( ) ) { }
			internal( type sentence_type, const std::string & name ) :
				sentence_type( sentence_type ), name( name ) { }
			internal( type ty, const variable & l, const sentence & r ) :
				sentence_type( ty ), name( l.name ), arguments( { r } ) { }
		};
		std::shared_ptr< internal > data;
		internal * operator ->( ) const { return data.get( ); }
		internal & operator * ( ) const { return * data; }
		template< typename ... T >
		auto type_restore_full( const T & ... t ) const
		{
			static_assert( std::tuple_size< std::tuple< T ... > >::value == 6, "should have six arguments" );
			return type_restore( t ..., error( ) );
		}
		template< typename ... T >
		auto type_restore( const T & ... t ) const
		{
			return type_restore_inner(
						extract< and_actor_helper >(
							t ...,
							make_and_actor(
								std::get< std::tuple_size< std::tuple< T ... > >::value - 1 >( std::tie( t ... ) ) ) ),
						extract< or_actor_helper >(
							t ...,
							make_or_actor(
								std::get< std::tuple_size< std::tuple< T ... > >::value - 1 >( std::tie( t ... ) ) ) ),
						extract< not_actor_helper >(
							t ...,
							make_not_actor(
								std::get< std::tuple_size< std::tuple< T ... > >::value - 1 >( std::tie( t ... ) ) ) ),
						extract< all_actor_helper >(
							t ...,
							make_all_actor(
								std::get< std::tuple_size< std::tuple< T ... > >::value - 1 >( std::tie( t ... ) ) ) ),
						extract< some_actor_helper >(
							t ...,
							make_some_actor(
								std::get< std::tuple_size< std::tuple< T ... > >::value - 1 >( std::tie( t ... ) ) ) ),
						extract< atomic_actor_helper >(
							t ...,
							make_atomic_actor(
								std::get< std::tuple_size< std::tuple< T ... > >::value - 1 >( std::tie( t ... ) ) ) ) );
		}
		template< typename T1, typename T2, typename T3, typename T4, typename T5, typename T6 >
		auto type_restore_inner(
				const and_actor< T1 > & and_func,
				const or_actor< T2 > & or_func,
				const not_actor< T3 > & not_func,
				const all_actor< T4 > & all_func,
				const some_actor< T5 > & some_func,
				const atomic_actor< T6 > & atomic_func ) const
		{
			switch ( (*this)->sentence_type )
			{
			case type::logical_and:
				return and_func(
							boost::get< sentence >( (*this)->arguments[0] ),
							boost::get< sentence >( (*this)->arguments[1] ) );
			case type::logical_not:
				return not_func( boost::get< sentence >( (*this)->arguments[0] ) );
			case type::logical_or:
				return or_func(
							boost::get< sentence >( (*this)->arguments[0] ),
							boost::get< sentence >( (*this)->arguments[1] ) );
			case type::all:
				return all_func(
							variable( (*this)->name ),
							boost::get< sentence >( (*this)->arguments[0] ) );
			case type::some:
				return some_func(
							variable( (*this)->name ),
							boost::get< sentence >( (*this)->arguments[0] ) );
			case type::atomic:
				return atomic_func( boost::get< atomic_sentence >( (*this)->arguments[0] ) );
			}
			throw std::invalid_argument( "unknown enum type" );
		}
		bool is_atom( ) const { return (*this)->sentence_type == type::atomic; }
		explicit operator std::string( ) const;
		sentence( type ty, const variable & l, const sentence & r ) : data( new internal( ty, l, r ) ) { }
		template< typename ... T >
		sentence( type ty, const T & ... t ) : data( new internal( ty, t ... ) ) { }
		template< typename ... T >
		sentence( type ty, const T & ... t, const std::initializer_list< sentence > & vec ) :
			data( new internal( ty, t ..., vec ) ) { }
		template< typename ... T >
		sentence( type ty, const T & ... t, const std::initializer_list< term > & vec ) :
			data( new internal( ty, t ..., vec ) ) { }
		sentence( const sentence & sen ) : data( sen.data ) { }
		sentence( ) { }
		sentence( const atomic_sentence & as ) : sentence( type::atomic, as ) { }
		bool operator == ( const sentence & comp ) const { return !( (*this) < comp || comp < (*this) ); }
		bool operator != ( const sentence & comp ) const { return ! ( (*this) == comp ); }
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
		bool operator < ( const sentence & comp ) const
		{
			if ( length( ) < comp.length( ) ) { return true; }
			if ( length( ) > comp.length( ) ) { return false; }
			return static_cast< std::string >( * this ) < static_cast< std::string >( comp );
		}
		bool have_quantifier( ) const;
		bool is_in_prenex_form( ) const;
		sentence standardize_bound_variable( ) const
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
		sentence standardize_bound_variable( std::set< std::string > & term_map ) const;
		sentence move_quantifier_out( ) const;
		sentence skolemization_remove_existential( std::set< variable > & previous_quantifier ) const;
		sentence skolemization_remove_universal( std::set< variable > & previous_quantifier ) const;
		sentence skolemization_remove_existential( ) const;
		sentence skolemization_remove_universal( ) const;
		sentence drop_existential( ) const;
		sentence drop_universal( ) const;
		sentence rectify( ) const;
		sentence rectify(
					std::set< variable > & used_quantifier,
					const std::set< variable > & free_variable,
					std::set< std::string > & used_name ) const;
		template< typename OUTITER >
		OUTITER used_name( OUTITER result ) const;
		explicit operator bool ( ) const { return data.get( ) != nullptr; }
		void swap( sentence & sen ) { data.swap( sen.data ); }
		sentence restore_quantifier_existential( ) const;
		sentence restore_quantifier_universal( ) const;
		template< typename OSTREAM >
		friend OSTREAM & operator << ( OSTREAM & os, const sentence & sen )
		{ return os << static_cast< std::string >( sen ); }
	};
}
#include "implementation/sentence.hpp"
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
