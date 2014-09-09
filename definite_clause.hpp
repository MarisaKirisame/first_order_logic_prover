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
	struct knowledge_base
	{
		std::vector< definite_clause > kb;
		boost::optional< substitution > forward_chaining( const sentence & sen )
		{
			bool have_new_inference = true;
			while ( have_new_inference )
			{
				for ( size_t i = 0; i < kb.size( ); ++i )
				{
					const definite_clause & dc = kb[i];
				}
			}
		}
	};
}
#endif // DEFINITE_CLAUSE_HPP
