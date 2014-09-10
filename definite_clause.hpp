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
		std::vector< sentence > premise;
		sentence conclusion;
	};
}
#endif // DEFINITE_CLAUSE_HPP
