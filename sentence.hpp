#ifndef FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#include "function.hpp"
#include "predicate.hpp"
#include "term.hpp"
#include <boost/variant.hpp>
#include "proof_tree.hpp"
#include <boost/mpl/bool.hpp>
#define DEFINE_ACTOR( NAME )\
template< typename T >\
struct NAME ## _actor\
{\
	const T & t;\
	template< typename ... ARG > auto operator ( )( const ARG & ... arg ) const { return t( arg ... ); }\
	NAME ## _actor( const T & t ) : t( t ) { }\
};\
template< typename T >\
struct NAME ## _actor_helper : boost::mpl::true_{ };\
template< typename T > \
struct NAME ## _actor_helper< NAME ## _actor< T > > : boost::mpl::false_{ };
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
	struct extractor_helper;
	template< template< typename > class T >
	struct extractor
	{
		template< typename FIRST, typename ... REST >
		auto operator( )( const FIRST & f, const REST & ... r ) const { return extractor_helper< T, T< decltype( f ) >::value >( f, r ... ); }
		auto operator ( )( ) const { return ignore::get( ); }
	};
	template< template< typename > class T >
	struct extractor_helper< T, true >
	{
		template< typename FIRST, typename ... REST >
		auto operator( )( const FIRST & f, const REST & ... ) const { return f; }
		auto operator ( )( ) const { return ignore::get( ); }
	};
	template< template< typename > class T >
	struct extractor_helper< T, false >
	{
		template< typename FIRST, typename ... REST >
		auto operator( )( const FIRST &, const REST & ... r ) const { return extractor< T >( )( r ... ); }
		auto operator ( )( ) const { return ignore::get( ); }
	};
	template< template< typename > class T, typename ... ARG >
	auto extract( const ARG & ... arg ) { return extractor< T >( )( arg ... ); }
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
		void type_restore( const T & ... t )
		{
			type_restore(
						extract< and_actor_helper >( t ... ),
						extract< or_actor_helper >( t ... ),
						extract< not_actor_helper >( t ... ),
						extract< all_actor_helper >( t ... ),
						extract< some_actor_helper >( t ... ),
						extract< equal_actor_helper >( t ... ),
						extract< predicate_actor_helper >( t ... ),
						extract< propositional_letter_actor_helper >( t ... ) );
		}
		template< typename T1, typename T2, typename T3, typename T4, typename T5, typename T6, typename T7, typename T8 >
		void type_restore(
				const T1 & and_func,
				const T2 & or_func,
				const T3 & not_func,
				const T4 & all_func,
				const T5 & some_func,
				const T6 & equal_func,
				const T7 & predicate_func,
				const T8 & propositional_letter_func ) const
		{
			switch ( (*this)->sentence_type )
			{
			case type::logical_and:
				and_func( boost::get< sentence >( (*this)->arguments[0] ), boost::get< sentence >( (*this)->arguments[1] ) );
				break;
			case type::logical_not:
				not_func( boost::get< sentence >( (*this)->arguments[0] ) );
				break;
			case type::logical_or:
				or_func( boost::get< sentence >( (*this)->arguments[0] ), boost::get< sentence >( (*this)->arguments[1] ) );
				break;
			case type::all:
				all_func( variable( (*this)->name ), boost::get< sentence >( (*this)->arguments[1] ) );
				break;
			case type::some:
				some_func( variable( (*this)->name ), boost::get< sentence >( (*this)->arguments[1] ) );
				break;
			case type::equal:
				equal_func( boost::get< term >( (*this)->arguments[0] ), boost::get< term >( (*this)->arguments[1] ) );
				break;
			case type::predicate:
			{
				std::vector< term > arg;
				std::transform( (*this)->arguments, (*this)->arguments, std::back_inserter( arg ), [](const auto & s){ return boost::get< term >( s ); } );
				predicate_func( (*this)->name, arg );
				break;
			}
			case type::propositional_letter:
				propositional_letter_func( (*this)->name );
				break;
			}
		}
		/*explicit operator std::string( ) const
		{
			switch ( (*this)->as_type )
			{
			case type::equal:
				return "(" + static_cast< std::string >( (*this)->arguments[0] ) + "=" + static_cast< std::string >( (*this)->arguments[1] ) + ")";
			case type::predicate:
			{
				std::string stack;
				for ( const auto & i : (*this)->arguments )
				{
					if( ! stack.empty( ) ) { stack += ", "; };
					stack += static_cast< std::string >( i );
				}
				return (*this)->name + "(" + stack + ")";
			}
			case type::propositional_letter:
				return static_cast< std::string >( (*this)->arguments[0] );
			}
		}
		explicit operator std::string( ) const
		{
			switch ( (*this)->cs_type )
			{
			case type::logical_and:
				return
						static_cast< std::string >( boost::get< sentence >( (*this)->arguments[0] ) ) +
						"/\\" +
						static_cast< std::string >( boost::get< sentence >( (*this)->arguments[1] ) );
			case type::logical_or:
				return
						static_cast< std::string >( boost::get< sentence >( (*this)->arguments[0] ) ) +
						"\\/" +
						static_cast< std::string >( boost::get< sentence >( (*this)->arguments[1] ) );
			case type::logical_not:
				return "!" + static_cast< std::string >( boost::get< sentence >( (*this)->arguments[0] ) );
			case type::all:
				return
						"∀" +
						static_cast< std::string >( boost::get< variable >( (*this)->arguments[0] ) ) +
						" " +
						static_cast< std::string >( boost::get< sentence >( (*this)->arguments[1] ) );
			case type::some:
				return
						"∃" +
						static_cast< std::string >( boost::get< variable >( (*this)->arguments[0] ) ) +
						" " +
						static_cast< std::string >( boost::get< sentence >( (*this)->arguments[1] ) );
			case type::atomic:
				return static_cast< std::string >( boost::get< atomic_sentence >( (*this)->arguments[0] ) );
			}
			throw std::invalid_argument( "unknown type" );
		}*/
		sentence( ) { }
		sentence( type ty, const variable & l, const sentence & r ) : data( new internal( ty, l, r ) ) { }
		template< typename ... T >
		sentence( type ty, const T & ... t ) : data( new internal( ty, t ... ) ) { }
		template< typename ... T, typename VEC >
		sentence( type ty, const T & ... t, const std::initializer_list< VEC > & vec ) : data( new internal( ty, t ..., vec ) ) { }
	};
}
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
