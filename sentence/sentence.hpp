#ifndef FIRST_ORDER_LOGIC_SENTENCE_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_SENTENCE_SENTENCE_HPP
#include <type_traits>
#include "function.hpp"
#include "predicate.hpp"
#include "term.hpp"
#include <boost/variant.hpp>
#include "constant.hpp"
#include <boost/iterator/transform_iterator.hpp>
#include "forward/first_order_logic.hpp"
#include "sentence_helper.hpp"
#include "TMP.hpp"
#include "converter.hpp"
#include "atomic_sentence.hpp"
#include "../cpp_common/named_parameter.hpp"
namespace first_order_logic
{
    DEFINE_ACTOR(and);
    DEFINE_ACTOR(or);
    DEFINE_ACTOR(not);
    DEFINE_ACTOR(all);
    DEFINE_ACTOR(some);
    DEFINE_ACTOR(atomic);
    struct substitution;
    template< typename T >
    struct sentence
    {
        struct internal
        {
            sentence_type type;
            std::string name;
            mutable std::string cache;
            std::vector
            <
                boost::variant
                <
                    boost::recursive_wrapper< sentence< T > >,
                    typename next_sentence_type< sentence< T > >::type
                >
            > arguments;
            internal( sentence_type st, const sentence< T > & r ) :
                type( st ), arguments( { r } ) { }
            internal( sentence_type st, const typename next_sentence_type< sentence< T > >::type & r ) :
                type( st ), arguments( { r } ) { }
            internal(
                    sentence_type st,
                    const std::initializer_list< typename next_sentence_type< sentence< T > >::type > & r ) :
                type( st ), arguments( r.begin( ), r.end( ) ) { }
            internal( sentence_type st, const std::initializer_list< sentence< T > > & r ) :
                type( st ), arguments( r.begin( ), r.end( ) ) { }
            internal( sentence_type st, const std::string & name ) :
                type( st ), name( name ) { }
            internal( sentence_type ty, const variable & l, const sentence< T > & r ) :
                type( ty ), name( l.name ), arguments( { r } ) { }
        };
        std::shared_ptr< internal > data;
        internal * operator ->( ) const { return data.get( ); }
        internal & operator * ( ) const { return * data; }
        template< typename ... ACTORS >
        struct full_type_restore
        {
            template< typename ACTOR, typename UNTESTED, typename PLACEHOLDER >
            struct have_operator_actor;
            template< typename UNTESTED, typename PLACEHOLDER >
            struct have_operator_actor< vector< >, UNTESTED, PLACEHOLDER > : std::false_type { };
            template< typename PLACEHOLDER >
            struct have_operator_actor< vector< >, set< >, PLACEHOLDER > : std::true_type { };
            template< typename V, typename PLACEHOLDER >
            struct have_operator_actor< V, set< >, PLACEHOLDER > : std::true_type { };
#define HAVE_OPERATOR_ACTOR_GENERATOR( actor_name, enum_name ) \
            template< typename F, typename ... R, typename S, typename PLACEHOLDER > \
            struct have_operator_actor< vector< actor_name, R ... >, S, PLACEHOLDER > : \
                have_operator_actor \
                < \
                    vector< R ... >, \
                    typename remove< S, set_c< sentence_type, enum_name > >::type, \
                    PLACEHOLDER \
                > { }; \
            template< typename F, typename ... R, typename PLACEHOLDER > \
            struct have_operator_actor< vector< actor_name, R ... >, set< >, PLACEHOLDER > : std::true_type { }
            HAVE_OPERATOR_ACTOR_GENERATOR( all_actor< F >, sentence_type::all );
            HAVE_OPERATOR_ACTOR_GENERATOR( some_actor< F >, sentence_type::some );
            HAVE_OPERATOR_ACTOR_GENERATOR( and_actor< F >, sentence_type::logical_and );
            HAVE_OPERATOR_ACTOR_GENERATOR( not_actor< F >, sentence_type::logical_not );
            HAVE_OPERATOR_ACTOR_GENERATOR( or_actor< F >, sentence_type::logical_or );
            HAVE_OPERATOR_ACTOR_GENERATOR( atomic_actor< F >, sentence_type::pass );
#undef HAVE_OPERATOR_ACTOR_GENERATOR
            template< typename ... ACTOR >
            struct have_atomic_actor;
            template< typename PLACEHOLDER >
            struct have_atomic_actor< PLACEHOLDER > : std::false_type { };
            template< typename FIRST, typename ... REST >
            struct have_atomic_actor< FIRST, REST ... > : have_atomic_actor< REST ... > { };
            template< typename FIRST, typename ... REST >
            struct have_atomic_actor< atomic_actor< FIRST >, REST ... > : std::true_type { };
            template< typename SEN, typename ... ACTOR >
            struct recurse_predicate;
            template< typename ... ACTOR >
            struct recurse_predicate< atomic_sentence, ACTOR ... > : std::true_type { };
            template< typename SEN, typename ... ACTOR >
            struct recurse_predicate< sentence< SEN >, ACTOR ... > :
                sentence< SEN >::template full_type_restore< ACTOR ... > { };
            constexpr static bool value =
                have_operator_actor< vector< ACTORS ... >, typename current_set< sentence  >::type, void >::value &&
                have_atomic_actor< ACTORS ..., void >::value &&
                recurse_predicate< typename next_sentence_type< sentence< T > >::type, ACTORS ... >::value;
        };
        template< typename RET, typename ... ACTORS >
        RET type_restore_full( const ACTORS & ... t ) const
        {
            static_assert( full_type_restore< ACTORS ... >::value, "type missing" );
            return type_restore< RET >( t ..., common::error< RET >( ) );
        }
        sentence( sentence_type ty,
                  const std::initializer_list< typename next_sentence_type< sentence< T > >::type > & il ) :
            data( new internal( ty, il ) ) { }
        sentence( sentence_type ty, const std::initializer_list< sentence< T > > & il ) :
            data( new internal( ty, il ) ) { }
        sentence( sentence_type ty, const typename next_sentence_type< sentence< T > >::type & il ) :
            data( new internal( ty, il ) ) { }
        sentence( sentence_type ty, const variable & l, const sentence< T > & r ) :
            data( new internal( ty, l, r ) ) { }
        sentence( const atomic_sentence & as ) :
            sentence( sentence_type::pass, typename next_sentence_type< sentence< T > >::type( as ) ) { }
        bool operator == ( const sentence< T > & comp ) const { return !( (*this) < comp || comp < (*this) ); }
        bool operator != ( const sentence< T > & comp ) const { return ! ( (*this) == comp ); }
        size_t length( ) const
        {
            return
                type_restore_full< size_t >
                (
                    make_all_actor( []( const variable &, const sentence< T > & s ) { return s.length( ); } ),
                    make_some_actor( []( const variable &, const sentence< T > & s ) { return s.length( ); } ),
                    make_atomic_actor( []( const atomic_sentence & )->size_t { return 0; } ),
                    make_and_actor(
                        []( const sentence< T > & l, const sentence< T > & r )
                        { return l.length( ) + r.length( ); } ),
                    make_or_actor(
                        []( const sentence< T > & l, const sentence< T > & r )
                        { return l.length( ) + r.length( ); } ),
                    make_not_actor(
                        []( const sentence< T > & sen ) { return sen.length( ); } )
                );
        }
        bool operator < ( const sentence< T > & comp ) const
        {
            if ( length( ) < comp.length( ) ) { return true; }
            if ( length( ) > comp.length( ) ) { return false; }
            return static_cast< std::string >( * this ) < static_cast< std::string >( comp );
        }
        explicit operator bool ( ) const { return data.get( ) != nullptr; }
        void swap( sentence< T > & sen ) { data.swap( sen.data ); }
        template< typename OSTREAM >
        friend OSTREAM & operator << ( OSTREAM & os, const sentence< T > & sen )
        { return os << static_cast< std::string >( sen ); }
        template
        <
            sentence_type st,
            bool = boost::hana::elem(
                    to_hana< typename current_set< sentence >::type >::value, boost::hana::type< std::integral_constant< sentence_type, st > > ),
            bool = std::is_same< typename next_sentence_type< sentence< T > >::type, atomic_sentence >::value
        >
        struct get_sentence_type;
        template< sentence_type st, bool b >
        struct get_sentence_type< st, true, b > { typedef sentence< T > type; };
        template< sentence_type st >
        struct get_sentence_type< st, false, true > { typedef no_such_sentence type; };
        template< sentence_type st >
        struct get_sentence_type< st, false, false >
        { typedef typename next_sentence_type< sentence< T >  >::type::template get_sentence_type< st >::type type; };
        typedef typename get_sentence_type< sentence_type::logical_and >::type and_sentence_type;
        typedef typename get_sentence_type< sentence_type::logical_or >::type or_sentence_type;
        typedef typename get_sentence_type< sentence_type::logical_not >::type not_sentence_type;
        typedef typename get_sentence_type< sentence_type::all >::type all_sentence_type;
        typedef typename get_sentence_type< sentence_type::some >::type some_sentence_type;
        template< sentence_type st, typename TO >
        struct can_convert_to;
        template< typename TO >
        struct can_convert_to< sentence_type::logical_not, sentence< TO > >
        {
            constexpr static bool value =
                    ! std::is_same
                    <
                        decltype( not_converter< TO >( )( std::declval< not_sentence_type >( ) ) ),
                        void
                    >::value;
        };
        template< typename TO >
        struct can_convert_to< sentence_type::logical_and, sentence< TO > >
        {
            constexpr static bool value =
                    ! std::is_same
                    <
                        decltype( and_converter< TO >( )(
                              std::declval< and_sentence_type >( ),
                              std::declval< and_sentence_type >( ) ) ),
                        void
                    >::value;
        };
        template< typename TO >
        struct can_convert_to< sentence_type::logical_or, sentence< TO > >
        {
            constexpr static bool value =
                    ! std::is_same
                    <
                        decltype( or_converter< TO >( )(
                            std::declval< or_sentence_type >( ),
                            std::declval< or_sentence_type >( ) ) ),
                        void
                    >::value;
        };
        template< typename TO >
        struct can_convert_to< sentence_type::all, sentence< TO > >
        {
            constexpr static bool value =
                    ! std::is_same
                    <
                        decltype( all_converter< TO >( )(
                            std::declval< variable >( ),
                            std::declval< all_sentence_type >( ) ) ),
                        void
                    >::value;
        };
        template< typename TO >
        struct can_convert_to< sentence_type::some, sentence< TO > >
        {
            constexpr static bool value =
                    ! std::is_same
                    <
                        decltype( some_converter< TO >( )(
                            std::declval< variable >( ),
                            std::declval< some_sentence_type >( ) ) ),
                        void
                    >::value;
        };
        template< typename RET, typename T1, typename T2, typename T3, typename T4, typename T5, typename T6 >
        RET type_restore_inner(
            const and_actor< T1 > & and_func,
            const or_actor< T2 > & or_func,
            const not_actor< T3 > & not_func,
            const all_actor< T4 > & all_func,
            const some_actor< T5 > & some_func,
            const atomic_actor< T6 > & atomic_func ) const
        {
            switch ( (*this)->type )
            {
                case sentence_type::logical_and:
                    return
                        common::make_expansion(
                            []( const std::false_type &, const auto &, const auto & )
                            { return common::error< RET >( )( ); },
                            [&]( const std::true_type &, const auto & l, const auto & r )
                            { return and_func( l, r ); } )
                            (
                                have
                                <
                                    typename current_set< sentence< T > >::type,
                                    set_c< sentence_type, sentence_type::logical_and >
                                >( ),
                                boost::get< sentence< T > >( (*this)->arguments[0] ),
                                boost::get< sentence< T > >( (*this)->arguments[1] )
                            );
                case sentence_type::logical_not:
                    return
                        common::make_expansion(
                            []( const std::false_type &, const auto & ) { return common::error< RET >( )( ); },
                            [&]( const std::true_type &, const auto & s ) { return not_func( s ); } )
                            (
                                have
                                <
                                    typename current_set< sentence< T >  >::type,
                                    set_c< sentence_type, sentence_type::logical_not >
                                >( ),
                                boost::get< sentence< T > >( (*this)->arguments[0] )
                            );
                case sentence_type::logical_or:
                    return
                        common::make_expansion(
                            []( const std::false_type &, const auto &, const auto & )
                            { return common::error< RET >( )( ); },
                            [&]( const std::true_type &, const auto & l, const auto & r )
                            { return or_func( l, r ); } )
                            (
                                have
                                <
                                    typename current_set< sentence< T >  >::type,
                                    set_c< sentence_type, sentence_type::logical_or >
                                >( ),
                                boost::get< sentence< T > >( (*this)->arguments[0] ),
                                boost::get< sentence< T > >( (*this)->arguments[1] )
                            );
                case sentence_type::all:
                    return
                        common::make_expansion(
                            []( const std::false_type &, const auto & ) { return common::error< RET >( )( ); },
                            [&]( const std::true_type &, const auto & s )
                            { return all_func( variable( (*this)->name ), s ); } )
                            (
                                have
                                <
                                    typename current_set< sentence< T >  >::type,
                                    set_c< sentence_type, sentence_type::all >
                                >( ),
                                boost::get< sentence< T > >( (*this)->arguments[0] )
                            );
                case sentence_type::some:
                    return
                        common::make_expansion(
                            []( const std::false_type &, const auto & ) { return common::error< RET >( )( ); },
                            [&]( const std::true_type &, const auto & s )
                            { return some_func( variable( (*this)->name ), s ); } )
                            (
                                have
                                <
                                    typename current_set< sentence< T >  >::type,
                                    set_c< sentence_type, sentence_type::some >
                                >( ),
                                boost::get< sentence< T > >( (*this)->arguments[0] )
                            );
                case sentence_type::pass:
                    return
                        common::make_expansion(
                            [&]( const atomic_sentence & as ) { return atomic_func( as ); },
                            [&]( const auto & n )
                            {
                                return n.template type_restore< RET >
                                        (
                                            and_func,
                                            or_func,
                                            not_func,
                                            all_func,
                                            some_func,
                                            atomic_func,
                                            common::error< RET >( )
                                        );
                            } )
                            ( boost::get< typename next_sentence_type< sentence< T > >::type >(
                                  (*this)->arguments[0] ) );
                default:
                    throw std::invalid_argument( "unknown sentence_type in sentence::type_restore" );
            }
        }

        template< typename RET, typename ... ACTORS >
        RET type_restore( const ACTORS & ... t ) const
        {
            return type_restore_inner< RET >(
                common::extract< and_actor_helper >(
                    t ...,
                    make_and_actor(
                        std::get
                        < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
                common::extract< or_actor_helper >(
                    t ...,
                    make_or_actor(
                        std::get
                        < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
                common::extract< not_actor_helper >(
                    t ...,
                    make_not_actor(
                        std::get
                        < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
                common::extract< all_actor_helper >(
                    t ...,
                    make_all_actor(
                        std::get
                        < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
                common::extract< some_actor_helper >(
                    t ...,
                    make_some_actor(
                        std::get
                        < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
                common::extract< atomic_actor_helper >(
                    t ...,
                    make_atomic_actor(
                        std::get
                        < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ) );
        }

        template
        <
            typename TO,
            typename =
            std::enable_if_t
            <
                can_convert_to< sentence_type::logical_and, sentence< TO > >::value &&
                can_convert_to< sentence_type::logical_or, sentence< TO > >::value &&
                can_convert_to< sentence_type::logical_not, sentence< TO > >::value &&
                can_convert_to< sentence_type::all, sentence< TO > >::value &&
                can_convert_to< sentence_type::some, sentence< TO > >::value
            >
        >
        operator sentence< TO >( ) const
        {
            return type_restore_full< sentence< TO > >(
                        make_and_actor(
                            []( const auto & l, const auto & r ) { return and_converter< TO >( )( l, r ); } ),
                        make_or_actor(
                            []( const auto & l, const auto & r ) { return or_converter< TO >( )( l, r ); } ),
                        make_not_actor(
                            []( const auto & t ) { return not_converter< TO >( )( t ); } ),
                        make_all_actor(
                            []( const variable & v, const auto & t ) { return all_converter< TO >( )( v, t ); } ),
                        make_some_actor(
                            []( const variable & v, const auto & t )
                            { return some_converter< TO >( )( v, t ); } ),
                        make_atomic_actor( []( const atomic_sentence & as ) { return as; } ) );
        }

        operator std::string( ) const
        {
            if ( ! (*this)->cache.empty( ) ) { return (*this)->cache; }
            (*this)->cache =
                    "(" +
                    type_restore_full< std::string >
                    (
                        make_and_actor(
                            [&]( const sentence< T > & l, const sentence< T > & r )
                            {
                                return
                                        static_cast< std::string >( l ) +
                                        "/\\" +
                                        static_cast< std::string >( r );
                            } ),
                        make_some_actor(
                            [&]( const variable & var, const sentence< T > & sen )
                            {
                                return
                                        "∃" +
                                        var.name +
                                        " " +
                                        static_cast< std::string >( sen );
                            } ),
                        make_all_actor(
                            [&]( const variable & var, const sentence< T > & sen )
                            {
                                return
                                        "∀" +
                                        var.name +
                                        " " +
                                        static_cast< std::string >( sen );
                            } ),
                        make_or_actor(
                            [&]( const sentence< T > & l, const sentence< T > & r )
                            {
                                return
                                        static_cast< std::string >( l ) +
                                        "\\/" +
                                        static_cast< std::string >( r );
                            } ),
                        make_not_actor(
                            [&]( const sentence< T > & sen )
                            { return "!" + static_cast< std::string >( sen ); } ),
                        make_atomic_actor(
                            [&]( const atomic_sentence & as )
                            { return static_cast< std::string >( as ); } )
                    ) +
                    ")";
            return (*this)->cache;
        }
    };
    typedef sentence< vector< set_c< sentence_type, sentence_type::logical_not > > > not_sen_type;
    static_assert( std::is_convertible< not_sen_type, free_sentence >::value, "must be convertible to free sentence" );
    static_assert( not_sen_type::can_convert_to< sentence_type::logical_and, free_sentence >::value, "" );
    static_assert( ! std::is_convertible< free_sentence, not_sen_type >::value, "must be convertible to free sentence" );
}
#endif // FIRST_ORDER_LOGIC_SENTENCE_SENTENCE_HPP
