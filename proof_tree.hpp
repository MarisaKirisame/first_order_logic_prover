#ifndef FIRST_ORDER_LOGIC_PROOF_TREE_HPP
#define FIRST_ORDER_LOGIC_PROOF_TREE_HPP
#include <memory>
#include <string>
#include <vector>
namespace first_order_logic
{
	struct proof_tree : std::enable_shared_from_this< proof_tree >
	{
		virtual ~proof_tree( ) { }
		proof_tree * parent;
		std::string str;
		std::vector< std::shared_ptr< proof_tree > > child;
		proof_tree( const std::string & str, const std::vector< std::shared_ptr< proof_tree > > & child = { } ) :
			proof_tree( nullptr, str, child ) { }
		proof_tree( proof_tree * parent,
					const std::string & str,
					const std::vector<std::shared_ptr<proof_tree> > & child )
			: parent( parent ), str( str ), child( child ) { }
		bool has_parent( ) const { return parent != nullptr; }
	};
}
#endif // THEOREM_PROVER_FIRST_ORDER_LOGIC_PROOF_TREE_HPP
