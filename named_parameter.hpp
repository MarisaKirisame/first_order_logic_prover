#ifndef ANYPLACE_PARAMETER_HPP
#define ANYPLACE_PARAMETER_HPP
#define DEFINE_ACTOR( NAME )\
template< typename T >\
struct NAME ## _actor\
{\
	T t;\
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
	template< typename RET = void >
	struct ignore
	{
		template< typename ... T >
		RET operator( )( const T & ... ) const { }
	};
	template< typename RET = void >
	struct error
	{
		template< typename ... T >
		RET operator( )( const T & ... ) const { throw std::logic_error( "unknown enum type" ); }
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
}
#endif // ANYPLACE_PARAMETER_HPP
