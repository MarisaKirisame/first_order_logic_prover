#ifndef SUBSTITUTION_HPP
#define SUBSTITUTION_HPP
#include "sentence.hpp"
#include <map>
#include <string>
#include "first_order_logic.hpp"
#include "algorithm"
#include <boost/optional.hpp>
#include "sentence.hpp"
namespace first_order_logic
{
	struct substitution
	{
		std::map< variable, term > data;
		term operator ( )( const term & t ) const;
		sentence operator ( )( const sentence & s ) const;
		substitution( const std::map< variable, term > & data ) : data( data ) { }
		substitution( ) { }
		bool operator ==( const substitution & s ) const { return data == s.data; }
		bool coherent( const substitution & comp ) const;
		static boost::optional< substitution > join( const substitution & l, const substitution & r );
	};
	boost::optional< substitution > unify( const term & p, const term & q, const substitution & sub );
	boost::optional< substitution > unify( const std::vector< term > & p, const std::vector< term > & q, const substitution & sub );
	boost::optional< substitution > unify( const variable & var, const term & t, const substitution & sub );
	boost::optional< substitution > unify( const term & p, const term & q, const substitution & sub );
	boost::optional< substitution > unify( const variable & var, const term & t, const substitution & sub );
	boost::optional< substitution > unify( const sentence & p, const sentence & q, const substitution & sub );
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
}
#endif // SUBSTITUTION_HPP
