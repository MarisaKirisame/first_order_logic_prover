#ifndef DEFINITE_CLAUSE_HPP
#define DEFINITE_CLAUSE_HPP
#include "term.hpp"
#include <vector>
#include "substitution.hpp"
#include "sentence.hpp"
namespace first_order_logic
{
	struct definite_clause
	{
		std::vector< atomic_sentence > premise;
		atomic_sentence conclusion;
		definite_clause( const std::vector< atomic_sentence > & p, const atomic_sentence & c ) :
			premise( p ), conclusion( c )
		{ assert( p.size( ) != 0 ); }
	};
}
#endif // DEFINITE_CLAUSE_HPP
