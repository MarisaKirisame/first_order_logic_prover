#ifndef FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#include "function.hpp"
#include "predicate.hpp"
#include "term.hpp"
#include <boost/variant.hpp>
#include "proof_tree.hpp"
#include <boost/mpl/bool.hpp>
#include "constant.hpp"
#define DEFINE_ACTOR( NAME )\
template< typename T >\
struct NAME ## _actor\
{\
	const T & t;\
	template< typename ... ARG > auto operator ( )( const ARG & ... arg ) const { return t( arg ... ); }\
	explicit NAME ## _actor( const T & t ) : t( t ) { }\
};\
template< typename T >\
struct NAME ## _actor_helper : boost::mpl::false_{ };\
template< typename T >\
struct NAME ## _actor_helper< NAME ## _actor< T > > : boost::mpl::true_{ };\
template< typename T >\
NAME ## _actor< T > make_ ## NAME ## _actor( const T & t ) { return NAME ## _actor< T >( t ); }
namespace first_order_logic
{
	DEFINE_ACTOR(and);
	DEFINE_ACTOR(or);
	DEFINE_ACTOR(not);
	DEFINE_ACTOR(all);
	DEFINE_ACTOR(some);
	DEFINE_ACTOR(equal);
	DEFINE_ACTOR(predicate);
	DEFINE_ACTOR(propositional_letter);
	struct ignore
	{
		template< typename ... T >
		void operator( )( const T & ... ) const { }
		static const ignore & get( )
		{
			static ignore ret;
			return ret;
		}
	};
	template< template< typename > class T, bool is_current >
	struct extractor;
	template< template< typename > class T >
	struct extractor< T, true >
	{
		template< typename FIRST, typename ... REST >
		auto operator( )( const FIRST & f, const REST & ... ) const { return f; }
	};
	template< template< typename > class T >
	struct extractor< T, false >
	{
		template< typename FIRST, typename SECOND, typename ... REST >
		auto operator( )( const FIRST &, const SECOND & sec, const REST & ... r ) const
		{ return extractor< T, T< SECOND >::value >( )( sec, r ... ); }
	};
	template< template< typename > class T, typename FIRST, typename ... REST >
	auto extract( const FIRST & f, const REST & ... r ) { return extractor< T, T< FIRST >::value >( )( f, r ... ); }
	struct sentence
	{
		enum class type { logical_and, logical_or, logical_not, all, some, equal, predicate, propositional_letter };
		struct internal
		{
			type sentence_type;
			std::string name;
			std::vector< boost::variant< boost::recursive_wrapper< sentence >, term > > arguments;
			internal( type sentence_type, const std::string & name, const auto & r ) :
				sentence_type( sentence_type ), name( name ), arguments( r.begin( ), r.end( ) ) { }
			internal( type sentence_type, const auto & r ) :
				sentence_type( sentence_type ), arguments( r.begin( ), r.end( ) ) { }
			internal( type sentence_type, const std::string & name ) :
				sentence_type( sentence_type ), name( name ) { }
			internal( type ty, const variable & l, const sentence & r ) : sentence_type( ty ), name( l.name ), arguments( { r } ) { }
		};
		std::shared_ptr< internal > data;
		internal * operator ->( ) const { return data.get( ); }
		internal & operator * ( ) const { return * data; }
		template< typename ... T >
		auto type_restore_full( const T & ... t ) const
		{
			static_assert( std::tuple_size< std::tuple< T ... > >::value == 8, "should be eight arguments" );
			return type_restore( t ... );
		}
		template< typename ... T >
		auto type_restore( const T & ... t ) const
		{
			return type_restore_inner(
						extract< and_actor_helper >( t ..., make_and_actor( ignore::get( ) ) ),
						extract< or_actor_helper >( t ..., make_or_actor( ignore::get( ) ) ),
						extract< not_actor_helper >( t ..., make_not_actor( ignore::get( ) ) ),
						extract< all_actor_helper >( t ..., make_all_actor( ignore::get( ) ) ),
						extract< some_actor_helper >( t ..., make_some_actor( ignore::get( ) ) ),
						extract< equal_actor_helper >( t ..., make_equal_actor( ignore::get( ) ) ),
						extract< predicate_actor_helper >( t ..., make_predicate_actor( ignore::get( ) ) ),
						extract< propositional_letter_actor_helper >( t ..., make_propositional_letter_actor( ignore::get( ) ) ) );
		}
		template< typename T1, typename T2, typename T3, typename T4, typename T5, typename T6, typename T7, typename T8 >
		auto type_restore_inner(
				const and_actor< T1 > & and_func,
				const or_actor< T2 > & or_func,
				const not_actor< T3 > & not_func,
				const all_actor< T4 > & all_func,
				const some_actor< T5 > & some_func,
				const equal_actor< T6 > & equal_func,
				const predicate_actor< T7 > & predicate_func,
				const propositional_letter_actor< T8 > & propositional_letter_func ) const
		{
			switch ( (*this)->sentence_type )
			{
			case type::logical_and:
				return and_func( boost::get< sentence >( (*this)->arguments[0] ), boost::get< sentence >( (*this)->arguments[1] ) );
			case type::logical_not:
				return not_func( boost::get< sentence >( (*this)->arguments[0] ) );
			case type::logical_or:
				return or_func( boost::get< sentence >( (*this)->arguments[0] ), boost::get< sentence >( (*this)->arguments[1] ) );
			case type::all:
				return all_func( variable( (*this)->name ), boost::get< sentence >( (*this)->arguments[1] ) );
			case type::some:
				return some_func( variable( (*this)->name ), boost::get< sentence >( (*this)->arguments[1] ) );
			case type::equal:
				return equal_func( boost::get< term >( (*this)->arguments[0] ), boost::get< term >( (*this)->arguments[1] ) );
			case type::predicate:
			{
				std::vector< term > arg;
				std::transform(
					(*this)->arguments.begin( ),
					(*this)->arguments.end( ),
					std::back_inserter( arg ),
					[](const auto & s){ return boost::get< term >( s ); } );
				return predicate_func( (*this)->name, arg );
			}
			case type::propositional_letter:
				return propositional_letter_func( (*this)->name );
			}
		}
		explicit operator std::string( ) const
		{
			return
				"(" +
				type_restore_full
				(
					make_and_actor(
						[&]( const sentence & l, const sentence & r )
						{
							return
								static_cast< std::string >( l ) +
								"/\\" +
									static_cast< std::string >( r );
						} ),
					make_some_actor(
						[&]( const variable & var, const sentence & sen )
						{
							return
								"∃" +
								var.name +
								" " +
								static_cast< std::string >( sen );
						} ),
					make_all_actor(
						[&]( const variable & var, const sentence & sen )
						{
							return
								"∀" +
								var.name +
								" " +
								static_cast< std::string >( sen );
						} ),
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							return
								static_cast< std::string >( l ) +
								"\\/" +
								static_cast< std::string >( r );
						} ),
					make_not_actor( [&]( const sentence & sen ){ return "!" + static_cast< std::string >( sen ); } ),
					make_equal_actor(
						[&]( const term & l, const term & r )
						{ return static_cast< std::string >( l ) + "=" + static_cast< std::string >( r ); } ),
					make_predicate_actor(
						[&]( const std::string & str, const std::vector< term > & vec )
						{
							std::string stack;
							auto it = vec.begin( );
							goto http;
							while ( it != vec.end( ) )
							{
								stack += ", ";
								http://marisa.moe
								stack += static_cast< std::string >( * it );
								++it;
							}
							return str + "(" + stack + ")";
						} ),
					make_propositional_letter_actor( [&]( const std::string & str ){ return str; } )
				) +
				")";
		}
		sentence( ) { }
		sentence( type ty, const variable & l, const sentence & r ) : data( new internal( ty, l, r ) ) { }
		template< typename ... T >
		sentence( type ty, const T & ... t ) : data( new internal( ty, t ... ) ) { }
		template< typename ... T, typename VEC >
		sentence( type ty, const T & ... t, const std::initializer_list< VEC > & vec ) : data( new internal( ty, t ..., vec ) ) { }
		size_t length( ) const
		{
			return
				1 +
				type_restore_full
				(
					make_all_actor( []( const variable &, const sentence & s ){ return s.length( ); } ),
					make_some_actor( []( const variable &, const sentence & s ){ return s.length( ); } ),
					make_equal_actor( []( const term & l, const term & r ){ return l.length( ) + r.length( ); } ),
					make_predicate_actor(
						[]( const std::string &, const std::vector< term > & vec )
						{
							return std::accumulate(
										vec.begin( ),
										vec.end( ),
										static_cast< size_t >( 0 ),
										[]( size_t s, const term & t ){ return s + t.length( ); } );
						} ),
					make_propositional_letter_actor( []( const std::string & )->size_t{ return 0; } ),
					make_and_actor( []( const sentence & l, const sentence & r ){ return l.length( ) + r.length( ); } ),
					make_or_actor( []( const sentence & l, const sentence & r ){ return l.length( ) + r.length( ); } ),
					make_not_actor( []( const sentence & sen ){ return sen.length( ); } )
				);
		}
		std::set< function > functions( ) const
		{
			return
				type_restore_full
				(
					make_all_actor( []( const variable &, const sentence & s ){ return s.functions( ); } ),
					make_some_actor( []( const variable &, const sentence & s ){ return s.functions( ); } ),
					make_equal_actor(
							[]( const term & l, const term & r )
							{
								auto fl = l.functions( ), fr = r.functions( );
								std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
								return fr;
							} ),
					make_predicate_actor(
						[]( const std::string &, const std::vector< term > & vec )
						{
							std::set< function > ret;
							for ( const term & t : vec )
							{
								std::set< function > tem = t.functions( );
								std::copy( tem.begin( ), tem.end( ), std::inserter( ret, ret.begin( ) ) );
							}
							return ret;
						} ),
					make_propositional_letter_actor( []( const std::string & )->std::set< function >{ return { }; } ),
					make_and_actor(
							[]( const sentence & l, const sentence & r )
							{
								auto fl = l.functions( ), fr = r.functions( );
								std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
								return fr;
							} ),
					make_or_actor(
							[]( const sentence & l, const sentence & r )
							{
								auto fl = l.functions( ), fr = r.functions( );
								std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
								return fr;
							} ),
					make_not_actor( []( const sentence & sen ){ return sen.functions( ); } )
				);
		}
		std::set< predicate > predicates( ) const
		{
			return
				type_restore_full
				(
					make_all_actor( []( const variable &, const sentence & s ){ return s.predicates( ); } ),
					make_some_actor( []( const variable &, const sentence & s ){ return s.predicates( ); } ),
					make_equal_actor( []( const term &, const term & )->std::set< predicate > { return { }; } ),
					make_predicate_actor(
						[]( const std::string & str, const std::vector< term > & vec )->std::set< predicate >
						{ return { predicate( str, vec.size( ) ) }; } ),
					make_propositional_letter_actor( []( const std::string & )->std::set< predicate >{ return { }; } ),
					make_and_actor(
						[]( const sentence & l, const sentence & r )
						{
							auto fl = l.predicates( ), fr = r.predicates( );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_or_actor(
						[]( const sentence & l, const sentence & r )
						{
							auto fl = l.predicates( ), fr = r.predicates( );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_not_actor( []( const sentence & sen ){ return sen.predicates( ); } )
				);
		}
		std::set< variable > free_variables(  ) const
		{
			std::set< variable > bounded;
			auto ret = free_variables( bounded );
			for ( const variable & var : bounded ) { ret.erase( var ); }
			return ret;
		}
		std::set< variable > free_variables( std::set< variable > & bounded ) const
		{
			return
				type_restore_full
				(
					make_all_actor(
						[&]( const variable & var, const sentence & s )
						{
							bounded.insert( var );
							return s.free_variables( bounded );
						} ),
					make_some_actor(
						[&]( const variable & var, const sentence & s )
						{
							bounded.insert( var );
							return s.free_variables( bounded );
						} ),
					make_equal_actor( [&]( const term & l, const term & r )
					{
						auto fl = l.free_variables( ), fr = r.free_variables( );
						std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
						return fr;
					} ),
					make_predicate_actor(
						[&]( const std::string &, const std::vector< term > & vec )->std::set< variable >
						{
							std::set< variable > ret;
							for ( const term & t : vec )
							{
								std::set< variable > tem = t.free_variables( );
								std::copy( tem.begin( ), tem.end( ), std::inserter( ret, ret.begin( ) ) );
							}
							return ret;
						} ),
					make_propositional_letter_actor( []( const std::string & )->std::set< variable >{ return { }; } ),
					make_and_actor(
						[&]( const sentence & l, const sentence & r )
						{
							auto fl = l.free_variables( bounded ), fr = r.free_variables( bounded );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							auto fl = l.free_variables( bounded ), fr = r.free_variables( bounded );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_not_actor( [&]( const sentence & sen ){ return sen.free_variables( bounded ); } )
				);
		}
		bool have_equal( ) const
		{
			return
				type_restore_full
				(
					make_all_actor( [&]( const variable &, const sentence & s ) { return s.have_equal( ); } ),
					make_some_actor( [&]( const variable &, const sentence & s ) { return s.have_equal( ); } ),
					make_equal_actor( [&]( const term &, const term & ) { return true; } ),
					make_predicate_actor( [&]( const std::string &, const std::vector< term > & ){ return false; } ),
					make_propositional_letter_actor( []( const std::string & ) { return false; } ),
					make_and_actor( [&]( const sentence & l, const sentence & r ) { return l.have_equal( ) || r.have_equal( ); } ),
					make_or_actor( [&]( const sentence & l, const sentence & r ) { return l.have_equal( ) || r.have_equal( ); } ),
					make_not_actor( [&]( const sentence & sen ){ return sen.have_equal( ); } )
				);
		}
		std::set< constant > constants( ) const
		{
			return
				type_restore_full
				(
					make_all_actor( [&]( const variable &, const sentence & s ) { return s.constants( ); } ),
					make_some_actor( [&]( const variable &, const sentence & s ) { return s.constants( ); } ),
					make_equal_actor(
						[&]( const term & l, const term & r )
						{
							auto fl = l.constants( ), fr = r.constants( );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_predicate_actor(
						[&]( const std::string &, const std::vector< term > & vec )
						{
							std::set< constant > ret;
							for ( const term & t : vec )
							{
								std::set< constant > tem = t.constants( );
								std::copy( tem.begin( ), tem.end( ), std::inserter( ret, ret.begin( ) ) );
							}
							return ret;
						} ),
					make_propositional_letter_actor( []( const std::string & )->std::set< constant >{ return { }; } ),
					make_and_actor(
						[&]( const sentence & l, const sentence & r )
						{
							auto fl = l.constants( ), fr = r.constants( );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							auto fl = l.constants( ), fr = r.constants( );
							std::copy( fl.begin( ), fl.end( ), std::inserter( fr, fr.begin( ) ) );
							return fr;
						} ),
					make_not_actor( [&]( const sentence & sen ){ return sen.constants( ); } )
				);
		}
		bool operator < ( const sentence & comp ) const
		{
			if ( length( ) < comp.length( ) ) { return true; }
			if ( length( ) > comp.length( ) ) { return false; }
			return static_cast< std::string >( * this ) < static_cast< std::string >( * this );
		}
	};
}
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
