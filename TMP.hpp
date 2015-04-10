#ifndef FIRST_ORDER_LOGIC_TMP_HPP
#define FIRST_ORDER_LOGIC_TMP_HPP
#include <type_traits>
namespace first_order_logic
{
    //I KNOW I CAN USE BOOST::MPL
    //AND I TRY BUT THE RESULT IS IMPOSSIBLE TO DEBUG
    //SO I WILL REINVENT THE WHEEL UNTIL I CAN READ
    template< typename ... ELEMENT >
    struct set{ };
    template< typename SET, typename ELEMENT >
    struct have;
    template< typename FIRST, typename ... REST, typename ELEMENT >
    struct have< set< FIRST, REST ... >, set< ELEMENT > > : have< set< REST ... >, set< ELEMENT > > { };
    template< typename ... REST, typename ELEMENT >
    struct have< set< ELEMENT, REST ... >, set< ELEMENT > > : std::true_type { };
    template< typename ELEMENT >
    struct have< set< >, ELEMENT > : std::false_type { };
    template< typename F, typename ... R >
    struct have< set< >, set< F, R ... > > : std::false_type { };
    template< typename F, typename ... R, typename S >
    struct have< S, set< F, R ... > > :
            std::integral_constant< bool, have< S, set< F > >::value && have< S, set< R ... > >::value > { };
    template< typename S >
    struct have< S, set< > > : std::true_type { };
    template< typename L, typename R >
    struct subset;
    template< typename R >
    struct subset< set< >, R > { typedef set< > type; };
    template< typename L >
    struct subset< L, set< > > { typedef set< > type; };
    template< typename L, typename R >
    struct join;
    template< typename FIRST, typename ... REST, typename R >
    struct subset< set< FIRST, REST ... >, R >
    {
        typedef typename
        join
        <	typename
            std::conditional
            <
                have< R, set< FIRST > >::value,
                set< FIRST >,
                set< >
            >::type,
            typename subset< set< REST ... >, R >::type
        >::type type;
    };
    template< typename ... L, typename R >
    struct join< set< L ... >, set< R > >
    {
        typedef typename
        std::conditional
        <
            have< set< L ... >, set< R > >::value,
            set< L ... >,
            set< L ..., R >
        >::type type;
    };
    template< typename ... L, typename M, typename ... R >
    struct join< set< L ... >, set< M, R ... > >
    { typedef typename join< typename join< set< L ... >, set< M > >::type, set< R ... > >::type type; };
    template< typename T >
    struct join< set< >, T > { typedef T type; };
    template< typename T >
    struct join< T, set< > > { typedef T type; };
    template< >
    struct join< set< >, set< > > { typedef set< > type; };
    template< typename T >
    struct join< set< >, set< T > > { typedef set< T > type; };
    template< typename T >
    struct join< set< T >, set< > > { typedef set< T > type; };
    template< typename T, T ... rest >
    using set_c = set< std::integral_constant< T, rest > ... >;
    template< typename ... T >
    struct vector;
    template< typename T >
    struct is_vector : std::false_type { };
    template< typename ... T >
    struct is_vector< vector< T ... > > : std::true_type { };
    template< typename T > struct pop_front;
    template< typename F, typename ... R >
    struct pop_front< vector< F, R ... > > { typedef vector< R ... > type; };
    template< typename T > struct empty;
    template< typename F, typename ... R >
    struct empty< vector< F, R ... > > : std::false_type { };
    template< >
    struct empty< vector< > > : std::true_type { };
    template< typename F, typename ... R >
    struct empty< set< F, R ... > > : std::false_type { };
    template< >
    struct empty< set< > > : std::true_type { };
    template< typename T > struct front;
    template< typename F, typename ... R >
    struct front< vector< F, R ... > > { typedef F type; };
    template< typename T > struct back;
    template< typename F >
    struct back< vector< F > > { typedef F type; };
    template< typename F, typename ... R >
    struct back< vector< F, R ... > > { typedef typename back< vector< R ... > >::type type; };
    template< typename T, typename ADD > struct push_front;
    template< typename ADD, typename ... R >
    struct push_front< vector< R ... >, ADD > { typedef vector< ADD, R ... > type; };
    template< typename T, typename ADD > struct push_back;
    template< typename ADD, typename ... R >
    struct push_back< vector< R ... >, ADD > { typedef vector< R ..., ADD > type; };
    template< typename VECTOR >
    struct pop_back;
    template< typename T >
    struct pop_back< vector< T > > { typedef vector< > type; };
    template< typename F, typename ... REST >
    struct pop_back< vector< F, REST ... > >
    { typedef typename push_front< typename pop_back< vector< REST ... > >::type, F >::type type; };
    template< typename SET, typename INS >
    struct insert;
    template< typename ... ARG, typename ... INS >
    struct insert< set< ARG ... >, set< INS ... > > { typedef set< ARG ..., INS ... > type; };
    template< typename SET, typename REM >
    struct remove;
    template< typename ... ARG, typename REM >
    struct remove< set< ARG ... >, set< REM > >
    {
        template< typename ... A >
        struct inner;
        template< typename A >
        struct inner< A > { typedef set< > type; };
        template< typename ... A >
        struct inner< REM, A ... > { typedef typename inner< A ... >::type type; };
        template< typename F, typename ... A >
        struct inner< F, A ... >
        { typedef typename insert< typename inner< A ... >::type, set< F > >::type type; };
        typedef typename inner< ARG ..., void >::type type;
    };
    template< typename ... ARG, typename F, typename ... REM >
    struct remove< set< ARG ... >, set< F, REM ... > > :
            remove< typename remove< set< ARG ... >, set< REM ... > >::type, set< F > > { };
}
#endif //FIRST_ORDER_LOGIC_TMP_HPP
