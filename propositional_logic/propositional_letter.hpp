#ifndef THEOREM_PROVER_PROPOSITIONAL_PROPOSITIONAL_LOGIC_LETTER
#define THEOREM_PROVER_PROPOSITIONAL_PROPOSITIONAL_LOGIC_LETTER
#include <string>
namespace theorem_prover
{
	namespace propositional_logic
	{
		struct propositional_letter
		{
			std::string data;
			propositional_letter( std::string && d ) : data( std::move( d ) ) { }
			propositional_letter( const std::string & d ) : data( d ) { }
			bool operator < ( const propositional_letter & comp ) const { return data < comp.data; }
			bool operator == ( const propositional_letter & comp ) const { return data == comp.data; }
		};
	}
}
#endif //THEOREM_PROVER_PROPOSITIONAL_PROPOSITIONAL_LOGIC_LETTER
