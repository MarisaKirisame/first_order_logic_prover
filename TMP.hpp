#ifndef FIRST_ORDER_LOGIC_TMP_HPP
#define FIRST_ORDER_LOGIC_TMP_HPP
#include <type_traits>
#include <boost/hana.hpp>
#define REMOVE_TMP
namespace first_order_logic
{
    template< typename T > struct to_hana { };
    template< typename ... ELEMENT >
    struct set{ };
#ifndef REMOVE_TMP
#endif
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
        <   typename
            std::conditional
            <
                boost::hana::elem( to_hana< R >::value, boost::hana::type< FIRST > ),
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
            boost::hana::elem( to_hana< set< L ... > >::value, boost::hana::type< R > ),
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
    template< typename T > struct pop_front;
    template< typename F, typename ... R >
    struct pop_front< vector< F, R ... > > { typedef vector< R ... > type; };
    template< typename ... T >
    struct to_hana< vector< T ... > > { constexpr static auto value = boost::hana::tuple_t< T ... >; };
    template< typename ... T >
    struct to_hana< set< T ... > > { constexpr static auto value = boost::hana::set( boost::hana::type< T > ... ); };
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
    template< typename T >
    auto strip_type( boost::hana::_type< T > ) -> T { }
}
#endif //FIRST_ORDER_LOGIC_TMP_HPP
