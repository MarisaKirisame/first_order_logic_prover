#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "sentence.hpp"
#include <map>
#include <string>
#include "forward/first_order_logic.hpp"
#include "algorithm"
#include <boost/optional.hpp>
#include "sentence.hpp"
#include "atomic_sentence.hpp"
namespace first_order_logic
{
	struct substitution
	{
		std::map< variable, term > data;
		term operator ( )( const term & t ) const;
		atomic_sentence operator ( )( const atomic_sentence & as ) const;
		sentence operator ( )( const sentence & s ) const;
		substitution( const std::map< variable, term > & data ) : data( data ) { }
		substitution( ) { }
		bool operator ==( const substitution & s ) const { return data == s.data; }
		bool coherent( const substitution & comp ) const;
		static boost::optional< substitution > join( const substitution & l, const substitution & r );
	};
	boost::optional< substitution > unify(
			const term & p, const term & q, const substitution & sub );
	boost::optional< substitution > unify(
			const std::vector< term > & p, const std::vector< term > & q, const substitution & sub );
	boost::optional< substitution > unify(
			const variable & var, const term & t, const substitution & sub );
	boost::optional< substitution > unify(
			const term & p, const term & q, const substitution & sub );
	boost::optional< substitution > unify(
			const variable & var, const term & t, const substitution & sub );
	boost::optional< substitution > unify(
			const sentence & p, const sentence & q, const substitution & sub );
	boost::optional< substitution > unify(
			const atomic_sentence & p, const atomic_sentence & q, const substitution & sub );
	template< typename F, typename GENERATOR >
	void rename_variable( const term & t, const F & usable, const GENERATOR & gen, substitution & renamed );
	template< typename F, typename GENERATOR >
	void rename_variable( const variable & sen, const F & usable, const GENERATOR & gen, substitution & renamed );
	template< typename F, typename GENERATOR >
	void rename_variable( const sentence & sen, const F & usable, const GENERATOR & gen, substitution & renamed );
	template< typename INITER, typename F, typename GENERATOR >
	void rename_variable( INITER begin, INITER end, const F & usable, const GENERATOR & gen, substitution & renamed );
	template< typename ... T >
	boost::optional< substitution > unify( const T & ... );
	template< typename ... T >
	substitution rename_variable( const T & ... );
	atomic_sentence substitution::operator ( )( const atomic_sentence & as ) const
	{
		return as.type_restore_full
				(
					make_equal_actor( [&]( const term & l, const term & r ){ return make_equal( (*this)(l), (*this)(r) ); } ),
					make_predicate_actor(
						[&]( const std::string & str, const std::vector< term > & vec )
						{
							std::vector< term > tem;
							std::transform(
								vec.begin( ),
								vec.end( ),
								std::back_inserter( tem ),
								[&]( const term & te ){ return(*this)(te); } );
							return make_predicate( str, tem );
						} ),
					make_propositional_letter_actor(
						[&]( const std::string & str ){ return make_propositional_letter( str ); } )
				);
	}
}
#include "implementation/sentence.hpp"
#endif // SUBSTITUTION_HPP
