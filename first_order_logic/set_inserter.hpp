#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_SET_INSERTER
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_SET_INSERTER
namespace theorem_prover
{
	namespace first_order_logic
	{
		template< typename term >
		struct set_inserter
		{
			std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > & to;
			set_inserter( std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > & s ) : to( s ) { }
			set_inserter & operator ++ ( ) { return * this; }
			set_inserter & operator ++ ( int ) { return * this; }
			set_inserter & operator = ( const std::set< std::shared_ptr< term >, value_less< std::shared_ptr< term > > > & s )
			{
				to.insert( s.begin( ), s.end( ) );
				return * this;
			}
			set_inserter & operator * ( ) { return * this; }
		};
	}
}
#endif //THEOREM_PROVER_FIRST_ORDER_LOGIC_SET_INSERTER
