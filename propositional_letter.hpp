#ifndef GENTZEN_SYSTEM_PROPOSITIONAL_LETTER
#define GENTZEN_SYSTEM_PROPOSITIONAL_LETTER
#include <string>
namespace gentzen_system
{
	struct propositional_letter
	{
		std::string data;
		propositional_letter( std::string && d ) : data( std::move( d ) ) { }
		bool operator < ( const propositional_letter & comp ) const { return data < comp.data; }
		bool operator == ( const propositional_letter & comp ) const { return data == comp.data; }
	};
}
#endif //GENTZEN_SYSTEM_PROPOSITIONAL_LETTER
