#ifndef FUNCTION_OUTPUT_ITERATOR_H
#define FUNCTION_OUTPUT_ITERATOR_H
#include <memory>
namespace first_order_logic
{
	template< typename T >
	struct function_output_iterator : std::iterator< std::output_iterator_tag, T >
	{
		explicit function_output_iterator( ) { }
		explicit function_output_iterator( const T & f ) : f( std::shared_ptr< T >( new T( f ) ) ) {}
		struct proxy
		{
			proxy( std::shared_ptr< T > & f ) : f( f ) { }
			template< typename V >
			proxy & operator = ( const V & value )
			{
				(*f)(value);
				return *this;
			}
			const std::shared_ptr< T > & f;
		};
		proxy operator*( ) { return proxy( f ); }
		function_output_iterator & operator ++ ( ) { return *this; }
		function_output_iterator & operator ++ (int) { return *this; }
		function_output_iterator & operator = ( const function_output_iterator & p ) { f = p.f; return * this; }
		std::shared_ptr< T > f;
	};
	template< typename T >
	function_output_iterator< T > make_function_output_iterator( const T & f = T( ) ) { return function_output_iterator< T >( f ); }
}
#endif // FUNCTION_OUTPUT_ITERATOR_H
