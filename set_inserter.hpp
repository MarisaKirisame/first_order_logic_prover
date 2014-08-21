#ifndef FIRST_ORDER_LOGIC_SET_INSERTER
#define FIRST_ORDER_LOGIC_SET_INSERTER
namespace first_order_logic
{
	template< typename term, typename comp >
	struct set_inserter
	{
		std::set< std::shared_ptr< term >, comp > & to;
		set_inserter( std::set< std::shared_ptr< term >, comp > & s ) : to( s ) { }
		set_inserter & operator ++ ( ) { return * this; }
		set_inserter & operator ++ ( int ) { return * this; }
		set_inserter & operator = ( const std::set< std::shared_ptr< term >, comp > & s )
		{
			to.insert( s.begin( ), s.end( ) );
			return * this;
		}
		set_inserter & operator * ( ) { return * this; }
	};
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_SET_INSERTER
