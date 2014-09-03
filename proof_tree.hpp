#ifndef FIRST_ORDER_LOGIC_PROOF_TREE_HPP
#define FIRST_ORDER_LOGIC_PROOF_TREE_HPP
#include <memory>
#include <string>
#include <vector>
namespace first_order_logic
{
	struct proof_tree
	{
		struct internal : std::enable_shared_from_this< internal >
		{
			virtual ~internal( ) { }
			internal * parent;
			std::string str;
			std::vector< proof_tree > child;
			internal( const std::string & str, const std::vector< proof_tree > & child = { } ) :
				internal( nullptr, str, child ) { }
			internal
			(
				internal * parent,
				const std::string & str,
				const std::vector< proof_tree > & child
			) : parent( parent ), str( str ), child( child ) { }
		};
		std::shared_ptr< internal > data;
		bool has_parent( ) const { return data->parent != nullptr; }
		template< typename ... T >
		proof_tree( const T & ... t ) : data( new internal( t ... ) ) { }
		proof_tree( ) { }
		internal * operator ->( ) const { return data.get( ); }
		internal & operator * ( ) const { return * data; }
	};
}
#endif // THEOREM_PROVER_FIRST_ORDER_LOGIC_PROOF_TREE_HPP
