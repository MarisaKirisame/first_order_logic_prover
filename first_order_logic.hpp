#ifndef FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#define FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
#include "sentence.hpp"
#include "atomic_sentence.hpp"
#include "term.hpp"
#include "variable.hpp"
#include "forward/first_order_logic.hpp"
#include "sentence_helper.hpp"
namespace first_order_logic
{
    inline term make_function( const std::string & s, const std::vector< term > & t )
    { return term( term::type::function, s, t ); }

    inline term make_constant( const std::string & s )
    { return term( constant( s ) ); }

    inline term make_variable( const std::string & s )
    { return term( variable( s ) ); }

    inline atomic_sentence make_predicate( const std::string & s, const std::vector< term > & t )
    { return atomic_sentence( s, t ); }

    inline atomic_sentence make_propositional_letter( const std::string & s )
    { return make_predicate( s, { } ); }

    static_assert(
            std::is_convertible
            <
                sentence< vector< set_c< sentence_type, sentence_type::all > > >,
                sentence
                <
                    vector
                    <
                        set_c< sentence_type, sentence_type::logical_not >,
                        set_c< sentence_type, sentence_type::all >
                    >
                >
            >::value,
            "should be convertible" );

    static_assert(
            sentence< vector< set_c< sentence_type, sentence_type::all > > >::
                can_convert_to
                <
                    sentence_type::all,
                    sentence
                    <
                        vector
                        <
                            set_c< sentence_type, sentence_type::logical_not >,
                            set_c< sentence_type, sentence_type::all >
                        >
                    >
                >::value,
            "should be convertible" );

    template< typename T >
    typename add_sentence_front< T, set_c< sentence_type, sentence_type::logical_not > >::type
    make_not( const T & s )
    {
        typedef typename
        add_sentence_front
        <
            T,
            set_c< sentence_type, sentence_type::logical_not >
        >::type ret_type;
        return ret_type( sentence_type::logical_not, { static_cast< ret_type >( s ) } );
    }

    template< typename T1, typename T2 >
    typename add_sentence_front
    <
        typename std::common_type< T1, T2 >::type,
        set_c< sentence_type, sentence_type::logical_and >
    >::type
    make_and( const T1 & l, const T2 & r )
    {
        typedef
        typename add_sentence_front
        <
            typename std::common_type< T1, T2 >::type,
            set_c< sentence_type, sentence_type::logical_and >
        >::type ret_type;
        return
            ret_type( sentence_type::logical_and,
                    {
                        static_cast< ret_type >( l ),
                        static_cast< ret_type >( r )
                    } );
    }

    template< typename T1, typename T2 >
    typename add_sentence_front
    <
        typename std::common_type< T1, T2 >::type,
        set_c< sentence_type, sentence_type::logical_or >
    >::type
    make_or( const T1 & l, const T2 & r )
    {
        typedef
        typename add_sentence_front
        <
            typename std::common_type< T1, T2 >::type,
            set_c< sentence_type, sentence_type::logical_or >
        >::type ret_type;
        return
                ret_type( sentence_type::logical_or,
                {
                    static_cast< ret_type >( l ),
                    static_cast< ret_type >( r )
                } );
    }

    template< typename T >
    typename add_sentence_front< T, set_c< sentence_type, sentence_type::all > >::type
    make_all( const variable & l, const T & s )
    {
        typedef typename add_sentence_front< T, set_c< sentence_type, sentence_type::all > >::type ret_type;
        return ret_type( sentence_type::all, l, static_cast< ret_type >( s ) );
    }

    template< typename T >
    typename add_sentence_front< T, set_c< sentence_type, sentence_type::some > >::type
    make_some( const variable & l, const T & s )
    {
        typedef typename add_sentence_front< T, set_c< sentence_type, sentence_type::some > >::type ret_type;
        return ret_type( sentence_type::some, l, static_cast< ret_type >( s ) );
    }

    inline atomic_sentence make_equal( const term & l, const term & r )
    { return make_predicate( "=", { l, r } ); }

    template< typename T >
    T make_pass( const typename next_sentence_type< T >::type & t )
    { return T( sentence_type::pass, { t } ); }
}
#endif //FIRST_ORDER_LOGIC_FIRST_ORDER_LOGIC
