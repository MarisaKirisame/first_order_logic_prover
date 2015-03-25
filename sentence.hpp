#ifndef FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#define FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
#include <type_traits>
#include "function.hpp"
#include "predicate.hpp"
#include "term.hpp"
#include <boost/variant.hpp>
#include "proof_tree.hpp"
#include "function_output_iterator.hpp"
#include "constant.hpp"
#include <boost/iterator/transform_iterator.hpp>
#include "named_parameter.hpp"
#include "forward/first_order_logic.hpp"
#include "sentence_helper.hpp"
#include "TMP.hpp"
#include "converter.hpp"
#include "atomic_sentence.hpp"
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
        static_assert( is_vector< T >::value, "T should be vector" );
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
            return type_restore< RET >( t ..., error< RET >( ) );
        }
        template< typename RET, typename ... ACTORS >
        RET type_restore( const ACTORS & ... t ) const;
        template< typename RET, typename T1, typename T2, typename T3, typename T4, typename T5, typename T6 >
        RET type_restore_inner(
                const and_actor< T1 > & and_func,
                const or_actor< T2 > & or_func,
                const not_actor< T3 > & not_func,
                const all_actor< T4 > & all_func,
                const some_actor< T5 > & some_func,
                const atomic_actor< T6 > & atomic_func ) const;
        explicit operator std::string( ) const;
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
        size_t length( ) const;
        template< typename OUTITER >
        OUTITER functions( OUTITER result ) const;
        template< typename OUTITER >
        OUTITER predicates( OUTITER result ) const;
        template< typename OUTITER >
        OUTITER variables( OUTITER result ) const;
        template< typename OUTITER >
        OUTITER bounded_variables( OUTITER result ) const;
        template< typename OUTITER >
        OUTITER free_variables( OUTITER result ) const;
        bool have_equal( ) const;
        template< typename OUTITER >
        OUTITER constants( OUTITER result ) const;
        template< typename OUTITER >
        OUTITER cv( OUTITER result ) const
        {
            free_variables( constants( make_function_output_iterator(
                                           [&]( const auto & v ) { *result = term( v ); ++result; } ) ) );
            return result;
        }
        bool operator < ( const sentence< T > & comp ) const
        {
            if ( length( ) < comp.length( ) ) { return true; }
            if ( length( ) > comp.length( ) ) { return false; }
            return static_cast< std::string >( * this ) < static_cast< std::string >( comp );
        }
        sentence< T > standardize_bound_variable( ) const;
        sentence< T > standardize_bound_variable( std::set< std::string > & term_map ) const;
        typename
        move_operator_out
        <
            sentence< T >,
            set_c< sentence_type, sentence_type::all, sentence_type::some >
        >::type move_quantifier_out( ) const;
        typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
        skolemization_remove_existential( std::set< variable > & previous_quantifier ) const;
        typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
        skolemization_remove_universal( std::set< variable > & previous_quantifier ) const;
        typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
        skolemization_remove_existential( ) const;
        typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
        skolemization_remove_universal( ) const;
        typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
        drop_existential( ) const;
        typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
        drop_universal( ) const;
        sentence< T > rectify( ) const;
        sentence< T > rectify(
                std::set< variable > & used_quantifier,
                const std::set< variable > & free_variable,
                std::set< std::string > & used_name ) const;
        template< typename OUTITER >
        OUTITER used_name( OUTITER result ) const;
        explicit operator bool ( ) const { return data.get( ) != nullptr; }
        void swap( sentence< T > & sen ) { data.swap( sen.data ); }
        typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
        restore_quantifier_existential( ) const;
        typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
        restore_quantifier_universal( ) const;
        template< typename OSTREAM >
        friend OSTREAM & operator << ( OSTREAM & os, const sentence< T > & sen )
        { return os << static_cast< std::string >( sen ); }
        template
        <
            sentence_type st,
            bool = have< typename current_set< sentence  >::type, set_c< sentence_type, st > >::value,
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
            operator sentence< TO >( ) const;
        };
    typedef sentence< vector< set_c< sentence_type, sentence_type::logical_not > > > not_sen_type;
    static_assert( std::is_convertible< not_sen_type, free_sentence >::value, "must be convertible to free sentence" );
    static_assert( not_sen_type::can_convert_to< sentence_type::logical_and, free_sentence >::value, "" );
    static_assert( ! std::is_convertible< free_sentence, not_sen_type >::value, "must be convertible to free sentence" );

    template< typename T >
    size_t sentence< T >::length( ) const
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

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::functions( OUTITER result ) const
    {
        return
                type_restore_full< OUTITER >
                (
                    make_all_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { return s.functions( result ); } ),
                    make_some_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { return s.functions( result ); } ),
                    make_atomic_actor(
                        [&]( const atomic_sentence & as )
                        { return as.functions( result ); } ),
                    make_and_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { return l.functions( r.functions( result ) ); } ),
                    make_or_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { return l.functions( r.functions( result ) ); } ),
                    make_not_actor(
                        [&]( const sentence< T > & sen )
                        { return sen.functions( result ); } )
                );
    }

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::predicates( OUTITER result ) const
    {
        type_restore_full< void >
        (
            make_all_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { result = s.predicates( result ); } ),
            make_some_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { result = s.predicates( result ); } ),
            make_and_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { result = l.predicates( r.predicates( result ) ); } ),
            make_or_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { result = l.predicates( r.predicates( result ) ); } ),
            make_not_actor( [&]( const sentence< T > & sen ){ result = sen.predicates( result ); } ),
            make_atomic_actor( [&]( const atomic_sentence & as ) { result = as.predicates( result ); } )
        );
        return result;
    }

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::variables( OUTITER result ) const
    {
        type_restore_full
        (
            make_all_actor(
                [&]( const variable & var, const sentence< T > & s )
                {
                    *result = var;
                    ++result;
                    result = s.variables( result );
                } ),
            make_some_actor(
                [&]( const variable & var, const sentence< T > & s )
                {
                    *result = var;
                    ++result;
                    result = s.variables( result );
                } ),
            make_equal_actor(
                [&]( const term & l, const term & r )
                { result = l.variables( r.variables( result ) ); } ),
            make_predicate_actor(
                [&]( const std::string &, const std::vector< term > & vec )
                { for ( const term & t : vec ) { result = t.variables( result ); } } ),
            make_propositional_letter_actor( []( const std::string & ){ } ),
            make_and_actor(
                [&]( const sentence< T > & l, const sentence< T > & r )
                { result = l.variables( r.variables( result ) ); } ),
            make_or_actor(
                [&]( const sentence< T > & l, const sentence< T > & r )
                { result = l.variables( r.variables( result ) ); } ),
            make_not_actor( [&]( const sentence< T > & sen ){ result = sen.variables( result ); } )
        );
        return result;
    }

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::bounded_variables( OUTITER result ) const
    {
        type_restore_full
                (
                    make_all_actor(
                        [&]( const variable & var, const sentence< T > & s )
                        {
                            *result = var;
                            ++result;
                            result = s.bounded_variables( result );
                        } ),
                    make_some_actor(
                        [&]( const variable & var, const sentence< T > & s )
                        {
                            *result = var;
                            ++result;
                            result = s.bounded_variables( result );
                        } ),
                    make_equal_actor( [&]( const term &, const term & ) { } ),
                    make_predicate_actor(
                        [&]( const std::string &, const std::vector< term > & vec )
                        { for ( const term & t : vec ) { result = t.variables( result ); } } ),
                    make_propositional_letter_actor( []( const std::string & ){ } ),
                    make_and_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { result = l.bounded_variables( r.bounded_variables( result ) ); } ),
                    make_or_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { result = l.bounded_variables( r.bounded_variables( result ) ); } ),
                    make_not_actor(
                        [&]( const sentence< T > & sen ) { result = sen.bounded_variables( result ); } )
                );
        return result;
    }

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::free_variables( OUTITER result ) const
    {
        return type_restore_full< OUTITER >
        (
            make_all_actor(
                [&]( const variable &, const sentence< T > & s )
                { return s.free_variables( result ); } ),
            make_some_actor(
                [&]( const variable &, const sentence< T > & s )
                { return s.free_variables( result ); } ),
            make_atomic_actor(
                [&]( const atomic_sentence & as )
                { return as.free_variables( result ); } ),
            make_and_actor(
                [&]( const sentence< T > & l, const sentence< T > & r )
                { return l.free_variables( r.free_variables( result ) ); } ),
            make_or_actor(
                [&]( const sentence< T > & l, const sentence< T > & r )
                { return l.free_variables( r.free_variables( result ) ); } ),
            make_not_actor(
                [&]( const sentence< T > & sen )
                { return sen.free_variables( result ); } )
        );
    }

    template< typename T >
    bool sentence< T >::have_equal( ) const
    {
        return
            type_restore_full< bool >
            (
                make_all_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { return s.have_equal( ); } ),
                make_some_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { return s.have_equal( ); } ),
                make_atomic_actor(
                        [&]( const atomic_sentence & as )
                        { return as->atomic_sentence_type == atomic_sentence::type::equal; } ),
                make_and_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { return l.have_equal( ) || r.have_equal( ); } ),
                make_or_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { return l.have_equal( ) || r.have_equal( ); } ),
                make_not_actor(
                        [&]( const sentence< T > & sen ){ return sen.have_equal( ); } )
            );
    }

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::constants( OUTITER result ) const
    {
        return
            type_restore_full< OUTITER >
            (
                make_all_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return s.constants( result ); } ),
                make_some_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return s.constants( result ); } ),
                make_atomic_actor(
                    [&]( const atomic_sentence & as )
                    { return as.constants( result ); } ),
                make_and_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return l.constants( r.constants( result ) ); } ),
                make_or_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return l.constants( r.constants( result ) ); } ),
                make_not_actor(
                    [&]( const sentence< T > & sen )
                    { return sen.constants( result ); } )
            );
    }

    template< typename T >
    typename
    move_operator_out
    <
        sentence< T >,
        set_c< sentence_type, sentence_type::all, sentence_type::some >
    >::type
    sentence< T >::move_quantifier_out( ) const
    {
        typedef typename
        move_operator_out
        <
            sentence< T >,
            set_c< sentence_type, sentence_type::all, sentence_type::some >
        >::type ret_type;
        typedef sentence< vector< typename all_sentence_operator< sentence< T > >::type > > ground_type;
        auto switch_process =
                []( const auto & processed, const auto & unprocessed, const auto & make )
                {
                    return unprocessed.move_quantifier_out( ).template type_restore_full< ret_type >(
                               make_all_actor(
                                    [&]( const variable & v, const auto & s )
                                    {
                                        return make_all(
                                                    v,
                                                    make(
                                                        static_cast< ground_type >( s ),
                                                        static_cast< ground_type >( processed ) ).
                                                        move_quantifier_out( ) );
                                    } ),
                                make_some_actor(
                                    [&]( const variable & v, const auto & s )
                                    {
                                        return make_some(
                                                    v,
                                                    make(
                                                        static_cast< ground_type >( s ),
                                                        static_cast< ground_type >( processed ) ).
                                                        move_quantifier_out( ) );
                                    } ),
                                make_and_actor(
                                    [&]( const auto & l, const auto & r )->ret_type
                                    { return make( processed, make_and( l, r ) ); } ),
                                make_or_actor(
                                    [&]( const auto & l, const auto & r )->ret_type
                                    { return make( processed, make_or( l, r ) ); } ),
                                make_not_actor(
                                    [&]( const auto & s )->ret_type
                                    { return make( processed, make_not( s ) ); } ),
                                make_atomic_actor(
                                    [&]( const atomic_sentence & as )->ret_type
                                    { return make( processed, as ); } ) );
                };
        auto do_process =
                [&]( const auto & l, const auto & r, const auto & f )
                {
                    return l.move_quantifier_out( ).template type_restore_full< ret_type >(
                                make_all_actor( [&]( const variable & v, const auto & s )->ret_type
                                { return make_all( v, f( s, r ).move_quantifier_out( ) ); } ),
                                make_some_actor( [&]( const variable & v, const auto & s )->ret_type
                                { return make_some( v, f( s, r ).move_quantifier_out( ) ); } ),
                                make_and_actor( [&]( const auto & ll, const auto & rr )->ret_type
                                { return switch_process( make_and( ll, rr ), r, f ); } ),
                                make_or_actor( [&]( const auto & ll, const auto & rr )->ret_type
                                { return switch_process( make_or( ll, rr ), r, f ); } ),
                                make_not_actor(
                                    [&]( const auto & s ) { return switch_process( make_not( s ), r, f ); } ),
                                make_atomic_actor( [&]( const atomic_sentence & as )
                                { return switch_process( as, r, f ); } ) );
                };
        return type_restore_full< ret_type >
                (
                    make_all_actor(
                        [&]( const variable & v, const auto & s )
                        { return make_all( v, s.move_quantifier_out( ) ); } ),
                    make_some_actor(
                        [&]( const variable & v, const auto & s )
                        { return make_some( v, s.move_quantifier_out( ) ); } ),
                    make_atomic_actor( []( const atomic_sentence & as ) { return ret_type( as ); } ),
                    make_and_actor(
                        [&]( const auto & l, const auto & r )
                        {
                            return do_process(
                                        l,
                                        r,
                                        []( const auto & ll, const auto & rr )
                                        { return make_and( ll, rr ); } );
                        } ),
                    make_or_actor(
                        [&]( const auto & l, const auto & r )
                        {
                            return do_process(
                                        l,
                                        r,
                                        []( const auto & ll, const auto & rr )
                                        { return make_or( ll, rr ); } );
                        } ),
                    make_not_actor(
                        [&]( const auto & sen )->ret_type
                        {
                            return sen.move_quantifier_out( ).template type_restore_full< ret_type >(
                                        make_all_actor(
                                            [&]( const variable & v, const auto & s )
                                            {
                                                return
                                                    make_some(
                                                        v,
                                                        ( make_not( ground_type( s ) ) ).
                                                            move_quantifier_out( ) );
                                            } ),
                                        make_some_actor(
                                            [&]( const variable & v, const auto & s )
                                            {
                                                return
                                                    make_all(
                                                        v,
                                                        ( make_not( ground_type( s ) ) ).
                                                            move_quantifier_out( ) );
                                            } ),
                                        make_and_actor(
                                            [&]( const auto & ll, const auto & rr )->ret_type
                                            { return make_not( make_and( ll, rr ) ); } ),
                                        make_or_actor(
                                            [&]( const auto & ll, const auto & rr )->ret_type
                                            { return make_not( make_or( ll, rr ) ); } ),
                                        make_not_actor( [&]( const auto & s ) { return s; } ),
                                        make_atomic_actor(
                                            [&]( const atomic_sentence & as ) { return make_not( as ); } ) );
                        } )
                );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    sentence< T >::skolemization_remove_existential( ) const
    {
        std::set< variable > s;
        return skolemization_remove_existential( s );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    sentence< T >::skolemization_remove_universal( ) const
    {
        std::set< variable > s;
        return skolemization_remove_universal( s );
    }

    template< typename T >
    sentence< T > sentence< T >::rectify( ) const
    {
        std::set< variable > sv;
        std::set< std::string > used_name;
        std::set< variable > var;
        free_variables( std::inserter( var, var.begin( ) ) );
        this->used_name( std::inserter( used_name, used_name.begin( ) ) );
        return rectify( sv, var, used_name );
    }

    template< typename T >
    template< typename OUTITER >
    OUTITER sentence< T >::used_name( OUTITER result ) const
    {
        return
                type_restore_full< OUTITER >
                (
                    make_all_actor(
                        [&]( const variable & v, const auto & s )
                        {
                            * result = v.name;
                            ++result;
                            return s.used_name( result );
                        } ),
                    make_some_actor(
                        [&]( const variable & v, const auto & s )
                        {
                            * result = v.name;
                            ++result;
                            return s.used_name( result );
                        } ),
                    make_or_actor( [&]( const auto & l, const auto & r )
                        { return l.used_name( r.used_name( result ) ); } ),
                    make_and_actor( [&]( const auto & l, const auto & r )
                        { return l.used_name( r.used_name( result ) ); } ),
                    make_not_actor( [&]( const auto & sen ) { return sen.used_name( result ); } ),
                    make_atomic_actor( [&]( const atomic_sentence & sen ){ return sen.used_name( result ); } )
                );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    sentence< T >::drop_existential( ) const
    {
        return
                type_restore_full<
                    typename
                    remove_operator
                    <
                        sentence< T >,
                        set_c< sentence_type, sentence_type::some > >::type
                    >(
                        make_some_actor(
                            []( const variable &, const auto & se ) { return se.drop_existential( ); } ),
                        make_all_actor(
                            []( const variable & v, const auto & se )
                            { return make_all( v, se.drop_existential( ) ); } ),
                        make_atomic_actor( []( const atomic_sentence & as ) { return as; } ),
                        make_and_actor(
                            []( const auto & l, const auto & r )
                            { return make_and( l.drop_existential( ), r.drop_existential( ) ); } ),
                        make_or_actor(
                            []( const auto & l, const auto & r )
                            { return make_or( l.drop_existential( ), r.drop_existential( ) ); } ),
                        make_not_actor(
                            []( const auto & s ) { return make_not_actor( s.drop_existential( ) ); } ) );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    sentence< T >::drop_universal( ) const
    {
        return
                type_restore_full<
                    typename
                    remove_operator
                    <
                        sentence< T >,
                        set_c< sentence_type, sentence_type::all > >::type
                    >(
                        make_all_actor(
                            []( const variable &, const auto & se ) { return se.drop_universal( ); } ),
                        make_some_actor(
                            []( const variable & v, const auto & se )
                            { return make_some( v, se.drop_universal( ) ); } ),
                        make_atomic_actor( []( const atomic_sentence & as ) { return as; } ),
                        make_and_actor(
                            []( const auto & l, const auto & r )
                            { return make_and( l.drop_universal( ), r.drop_universal( ) ); } ),
                        make_or_actor(
                            []( const auto & l, const auto & r )
                            { return make_or( l.drop_universal( ), r.drop_universal( ) ); } ),
                        make_not_actor( []( const auto & s ) { return make_not( s.drop_universal( ) ); } ) );
    }

    template< typename T >
    typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    sentence< T >::restore_quantifier_existential( ) const
    {
        std::set< variable > var;
        free_variables( std::inserter( var, var.begin( ) ) );
        sentence< T > ret = * this;
        for ( const variable & v : var ) { ret = make_some( v, ret ); }
        return ret;
    }

    template< typename T >
    typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    sentence< T >::restore_quantifier_universal( ) const
    {
        std::set< variable > var;
        free_variables( std::inserter( var, var.begin( ) ) );
        sentence< T > ret = * this;
        for ( const variable & v : var ) { ret = make_all( v, ret ); }
        return ret;
    }

    template< typename T >
    template< typename RET, typename T1, typename T2, typename T3, typename T4, typename T5, typename T6 >
    RET sentence< T >::type_restore_inner(
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
                    misc::make_expansion(
                        []( const std::false_type &, const auto &, const auto & )
                        { return error< RET >( )( ); },
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
                    misc::make_expansion(
                        []( const std::false_type &, const auto & ) { return error< RET >( )( ); },
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
                    misc::make_expansion(
                        []( const std::false_type &, const auto &, const auto & )
                        { return error< RET >( )( ); },
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
                    misc::make_expansion(
                        []( const std::false_type &, const auto & ) { return error< RET >( )( ); },
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
                    misc::make_expansion(
                        []( const std::false_type &, const auto & ) { return error< RET >( )( ); },
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
                    misc::make_expansion(
                        [&]( const atomic_sentence & as ) { return atomic_func( as ); },
                        [&]( const typename next_sentence_type< sentence< T > >::type & n )
                        {
                            return n.template type_restore< RET >
                                    (
                                        and_func,
                                        or_func,
                                        not_func,
                                        all_func,
                                        some_func,
                                        atomic_func,
                                        error< RET >( )
                                    );
                        } )
                        ( boost::get< typename next_sentence_type< sentence< T > >::type >(
                              (*this)->arguments[0] ) );
            default:
                throw std::invalid_argument( "unknown sentence_type in sentence::type_restore" );
        }
    }

    template< typename T >
    template< typename RET, typename ... ACTORS >
    RET sentence< T >::type_restore( const ACTORS & ... t ) const
    {
        return type_restore_inner< RET >(
            extract< and_actor_helper >(
                t ...,
                make_and_actor(
                    std::get
                    < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
            extract< or_actor_helper >(
                t ...,
                make_or_actor(
                    std::get
                    < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
            extract< not_actor_helper >(
                t ...,
                make_not_actor(
                    std::get
                    < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
            extract< all_actor_helper >(
                t ...,
                make_all_actor(
                    std::get
                    < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
            extract< some_actor_helper >(
                t ...,
                make_some_actor(
                    std::get
                    < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
            extract< atomic_actor_helper >(
                t ...,
                make_atomic_actor(
                    std::get
                    < std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ) );
    }

    template< typename T >
    sentence< T > sentence< T >::standardize_bound_variable( ) const
    {
        std::set< std::string > term_map;
        cv( make_function_output_iterator(
                [&]( const term & t )
                {
                    assert( t->term_type == term::type::constant || t->term_type == term::type::variable );
                    term_map.insert( t->name );
                } ) );
        return standardize_bound_variable( term_map );
    }

    template< typename T >
    template< typename TO, typename >
    sentence< T >::operator sentence< TO >( ) const
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
}
#endif // FIRST_ORDER_LOGIC_COMPLEX_SENTENCE_HPP
