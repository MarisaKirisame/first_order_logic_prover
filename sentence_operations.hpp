#ifndef SENTENCE_OPERATIONS_HPP
#define SENTENCE_OPERATIONS_HPP
#include "sentence.hpp"
namespace first_order_logic
{
    template< typename T >
    sentence< T > standardize_bound_variable( const sentence< T > & self ,std::set< std::string > & term_map )
    {
        return
            self.type_restore_full
            (
                make_all_actor(
                    [&]( const variable & v, const sentence< T > & sen )
                    {
                        std::string gen_str = v.name;
                        while ( term_map.count( gen_str ) != 0 ) { gen_str += "_"; }
                        substitution sub( { std::make_pair( v, make_variable( gen_str ) ) } );
                        return make_all( v, sub( sen ) );
                    } ),
                make_some_actor(
                    [&]( const variable & v, const sentence< T > & sen )
                    {
                        std::string gen_str = v.name;
                        while ( term_map.count( gen_str ) != 0 ) { gen_str += "_"; }
                        substitution sub( { std::make_pair( v, make_variable( gen_str ) ) } );
                        return make_some( v, sub( sen ) );
                    } ),
                make_atomic_actor( [&]( const atomic_sentence & as ){ return sentence< T >( as ); } ),
                make_and_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    {
                        return make_and(
                                    l.standardize_bound_variable( term_map ),
                                    r.standardize_bound_variable( term_map ) );
                    } ),
                make_or_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    {
                        return make_or(
                                    l.standardize_bound_variable( term_map ),
                                    r.standardize_bound_variable( term_map ) );
                    } ),
                make_not_actor(
                    [&]( const sentence< T > & s )
                    { return make_not( s.standardize_bound_variable( term_map ) ); } )
            );
    }

    template< typename T >
    sentence< T >::operator std::string( ) const
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

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    skolemization_remove_existential( const sentence< T > & self, std::set< variable > & previous_quantifier )
    {
        typedef
        typename remove_operator
        <
            sentence< T >,
            set_c< sentence_type, sentence_type::some >
        >::type ret_type;
        return move_quantifier_out( rectify( self ) ).template type_restore_full
                <
                    typename remove_operator
                    <
                        sentence< T >,
                        set_c< sentence_type, sentence_type::some >
                    >::type
                >
        (
            make_all_actor(
                [&]( const variable & v, const auto & s )->ret_type
                {
                    previous_quantifier.insert( v );
                    return make_all( v, skolemization_remove_existential( s ) );
                } ),
            make_some_actor(
                [&]( const variable & v, const auto & s )->ret_type
                {
                    if ( previous_quantifier.empty( ) )
                    {
                        std::set< std::string > used;
                        cv( self,
                            make_function_output_iterator(
                                [&]( const term & t ){ used.insert( t->name ); } ) );
                        std::string unused = "_";
                        while ( used.count( unused ) != 0 ) { unused += "_"; }
                        return skolemization_remove_existential( substitution( { std::make_pair( v, make_variable( unused ) ) } )( s ) );
                    }
                    else
                    {
                        std::set< std::string > fun;
                        functions( self,
                                   make_function_output_iterator(
                                       [&]( const function & f ){ fun.insert( f.name ); } ) );
                        std::string unused = "_";
                        while ( fun.count( unused ) != 0 ) { unused += "_"; }
                        return
                            skolemization_remove_existential( substitution(
                                {
                                    std::make_pair(
                                        v,
                                        make_function(
                                            unused,
                                            std::vector< term >( previous_quantifier.begin( ),
                                    previous_quantifier.end( ) ) ) )
                                } )( s ) );
                    }
                } ),
            make_and_actor( []( const auto & l, const auto & r ) { return make_and( l, r ); } ),
            make_or_actor( []( const auto & l, const auto & r ) { return make_or( l, r ); } ),
            make_not_actor( [&]( const auto & l ) { return make_not( l ); } ),
            make_atomic_actor( []( const atomic_sentence & a ) { return a; } )
        );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    skolemization_remove_universal( const sentence< T > & self, std::set< variable > & previous_quantifier )
    {
        typedef
        typename remove_operator
        <
            sentence< T >,
            set_c< sentence_type, sentence_type::all >
        >::type ret_type;
        return move_quantifier_out( rectify( self ) ).template type_restore_full
                <
                    typename remove_operator
                    <
                        sentence< T >,
                        set_c< sentence_type, sentence_type::all >
                    >::type
                >
                (
                    make_some_actor(
                        [&]( const variable & v, const auto & s )->ret_type
                        {
                            previous_quantifier.insert( v );
                            return make_all( v, skolemization_remove_universal( s ) );
                        } ),
                    make_all_actor(
                        [&]( const variable & v, const auto & s )->ret_type
                        {
                            if ( previous_quantifier.empty( ) )
                            {
                                std::set< std::string > used;
                                cv( make_function_output_iterator(
                                    [&]( const term & t ){ used.insert( t->name ); } ) );
                                std::string unused = "_";
                                while ( used.count( unused ) != 0 ) { unused += "_"; }
                                return
                                    substitution( { std::make_pair( v, make_variable( unused ) ) } )( s ).
                                    skolemization_remove_universal( );
                            }
                            else
                            {
                                std::set< std::string > fun;
                                functions( make_function_output_iterator(
                                    [&]( const function & f ){ fun.insert( f.name ); } ) );
                                    std::string unused = "_";
                                    while ( fun.count( unused ) != 0 ) { unused += "_"; }
                                    return substitution(
                                        {
                                            std::make_pair(
                                                v,
                                                make_function(
                                                    unused,
                                                    std::vector< term >( previous_quantifier.begin( ),
                                                    previous_quantifier.end( ) ) ) )
                                        } )( s ).skolemization_remove_universal( );
                        }
                    } ),
                    make_and_actor( []( const auto & l, const auto & r ) { return make_and( l, r ); } ),
                    make_or_actor( []( const auto & l, const auto & r ) { return make_or( l, r ); } ),
                    make_not_actor( [&]( const auto & l ) { return make_not( l ); } ),
                    make_atomic_actor( []( const atomic_sentence & a ) { return a; } )
            );
    }

    template< typename T >
    sentence< T > rectify(
        const sentence< T > & self,
        std::set< variable > & used_quantifier,
        const std::set< variable > & free_variable,
        std::set< std::string > & used_name )
    {
        return self.template type_restore_full< sentence< T > >
                (
                    make_all_actor(
                        [&]( const variable & v, const auto & sen )->sentence< T >
                        {
                            if ( used_quantifier.count( v ) != 0 || free_variable.count( v ) != 0 )
                            {
                                std::string gen_str = v.name;
                                while ( used_quantifier.count( variable( gen_str ) ) != 0 ||
                                        free_variable.count( variable( gen_str ) ) != 0 ||
                                        used_name.count( gen_str ) != 0 ) { gen_str += "_"; }
                                used_name.insert( gen_str );
                                used_quantifier.insert( variable( gen_str ) );
                                return make_all(
                                            variable( gen_str ),
                                            substitution(
                                                { std::make_pair( v, make_variable( gen_str ) ) } )( sen ) );
                            }
                            return make_all( v, sen );
                        } ),
                    make_some_actor(
                        [&]( const variable & v, const auto & sen )->sentence< T >
                        {
                            if ( used_quantifier.count( v ) != 0 || free_variable.count( v ) != 0 )
                            {
                                std::string gen_str = v.name;
                                while ( used_quantifier.count( variable( gen_str ) ) != 0 ||
                                        free_variable.count( variable( gen_str ) ) != 0 ||
                                        used_name.count( gen_str ) != 0 ) { gen_str += "_"; }
                                used_name.insert( gen_str );
                                used_quantifier.insert( variable( gen_str ) );
                                return make_some(
                                            variable( gen_str ),
                                            substitution( { { v, make_variable( gen_str ) } } )( sen ) );
                            }
                            return make_some( v, sen );
                        } ),
                    make_atomic_actor(
                        [&]( const atomic_sentence & as )->sentence< T > { return sentence< T >( as ); } ),
                    make_or_actor(
                        [&]( const auto & l, const auto & r )-> sentence< T >
                        {
                            return make_or(
                                    rectify( l, used_quantifier, free_variable, used_name ),
                                    rectify( r, used_quantifier, free_variable, used_name ) );
                        } ),
                    make_and_actor(
                        [&]( const auto & l, const auto & r )-> sentence< T >
                        {
                            return make_and(
                                    rectify( l, used_quantifier, free_variable, used_name ),
                                    rectify( r, used_quantifier, free_variable, used_name ) );
                        } ),
                    make_not_actor(
                        [&]( const auto & sen )-> sentence< T >
                        { return make_not( rectify( sen, used_quantifier, free_variable, used_name ) ); } )
                );
    }

    template< typename T >
    sentence< T > rectify( const sentence< T > & self )
    {
        std::set< variable > sv;
        std::set< std::string > un;
        std::set< variable > var;
        free_variables( self, std::inserter( var, var.begin( ) ) );
        used_name( self, std::inserter( un, un.begin( ) ) );
        return rectify( self, sv, var, un );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    skolemization_remove_existential( const sentence< T > & self )
    {
        std::set< variable > s;
        return skolemization_remove_existential( self, s );
    }

    template< typename T, typename OUTITER >
    OUTITER functions( const sentence< T > & self, OUTITER result )
    {
        return
            self.template type_restore_full< OUTITER >
            (
                make_all_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return functions( s, result ); } ),
                make_some_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return functions( s, result ); } ),
                make_atomic_actor(
                    [&]( const atomic_sentence & as )
                    { return functions( as, result ); } ),
                make_and_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return functions( l, functions( r, result ) ); } ),
                make_or_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return functions( l, functions( r, result ) ); } ),
                make_not_actor(
                    [&]( const sentence< T > & sen )
                    { return functions( sen, result ); } )
            );
    }

    template< typename T, typename OUTITER >
    OUTITER predicates( const sentence< T > & self, OUTITER result )
    {
        self.template type_restore_full< void >
        (
            make_all_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { result = predicates( s, result ); } ),
            make_some_actor(
                        [&]( const variable &, const sentence< T > & s )
                        { result = predicates( s, result ); } ),
            make_and_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { result = predicates( l, predicates( r, result ) ); } ),
            make_or_actor(
                        [&]( const sentence< T > & l, const sentence< T > & r )
                        { result = predicates( l, predicates( r, result ) ); } ),
            make_not_actor( [&]( const sentence< T > & sen ) { result = predicates( sen, result ); } ),
            make_atomic_actor( [&]( const atomic_sentence & as ) { result = predicates( as, result ); } )
        );
        return result;
    }

    template< typename T, typename OUTITER >
    OUTITER variables( const sentence< T > & self, OUTITER result )
    {
        self.type_restore_full
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

    template< typename T, typename OUTITER >
    OUTITER bounded_variables( const sentence< T > & self, OUTITER result )
    {
        self.type_restore_full
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

    template< typename T, typename OUTITER >
    OUTITER free_variables( const sentence< T > & self, OUTITER result )
    {
        return self.template type_restore_full< OUTITER >
        (
            make_all_actor(
                [&]( const variable &, const sentence< T > & s )
                { return free_variables( s, result ); } ),
            make_some_actor(
                [&]( const variable &, const sentence< T > & s )
                { return free_variables( s, result ); } ),
            make_atomic_actor(
                [&]( const atomic_sentence & as )
                { return free_variables( as, result ); } ),
            make_and_actor(
                [&]( const sentence< T > & l, const sentence< T > & r )
                { return free_variables( l, free_variables( r, result ) ); } ),
            make_or_actor(
                [&]( const sentence< T > & l, const sentence< T > & r )
                { return free_variables( l, free_variables( r, result ) ); } ),
            make_not_actor(
                [&]( const sentence< T > & sen )
                { return free_variables( sen, result ); } )
        );
    }

    template< typename T >
    bool have_equal( const sentence< T > & self )
    {
        return
            self.template type_restore_full< bool >
            (
                make_all_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return have_equal( s ); } ),
                make_some_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return have_equal( s ); } ),
                make_atomic_actor(
                    [&]( const atomic_sentence & as )
                    { return as->atomic_sentence_type == atomic_sentence::type::equal; } ),
                make_and_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return have_equal( l ) || have_equal( r ); } ),
                make_or_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return have_equal( l ) || have_equal( r ); } ),
                make_not_actor(
                    [&]( const sentence< T > & sen ) { return have_equal( sen ); } )
            );
    }

    template< typename T, typename OUTITER >
    OUTITER constants( const sentence< T > & self, OUTITER result )
    {
        return
            self.template type_restore_full< OUTITER >
            (
                make_all_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return constants( s, result ); } ),
                make_some_actor(
                    [&]( const variable &, const sentence< T > & s )
                    { return constants( s, result ); } ),
                make_atomic_actor(
                    [&]( const atomic_sentence & as )
                    { return constants( as, result ); } ),
                make_and_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return constants( l, constants( r, result ) ); } ),
                make_or_actor(
                    [&]( const sentence< T > & l, const sentence< T > & r )
                    { return constants( l, constants( r, result ) ); } ),
                make_not_actor(
                    [&]( const sentence< T > & sen )
                    { return constants( sen, result ); } )
            );
    }

    template< typename T >
    typename
    move_operator_out
    <
        sentence< T >,
        set_c< sentence_type, sentence_type::all, sentence_type::some >
    >::type
    move_quantifier_out( const sentence< T > & self )
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
                    return move_quantifier_out( unprocessed ).template type_restore_full< ret_type >(
                               make_all_actor(
                                    [&]( const variable & v, const auto & s )
                                    {
                                        return make_all(
                                                    v,
                                                    move_quantifier_out( make(
                                                        static_cast< ground_type >( s ),
                                                        static_cast< ground_type >( processed ) ) ) );
                                    } ),
                                make_some_actor(
                                    [&]( const variable & v, const auto & s )
                                    {
                                        return make_some(
                                                    v,
                                                    move_quantifier_out( make(
                                                        static_cast< ground_type >( s ),
                                                        static_cast< ground_type >( processed ) ) ) );
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
                    return move_quantifier_out( l ).template type_restore_full< ret_type >(
                                make_all_actor( [&]( const variable & v, const auto & s )->ret_type
                                { return move_quantifier_out( make_all( v, f( s, r ) ) ); } ),
                                make_some_actor( [&]( const variable & v, const auto & s )->ret_type
                                { return move_quantifier_out( make_some( v, f( s, r ) ) ); } ),
                                make_and_actor( [&]( const auto & ll, const auto & rr )->ret_type
                                { return switch_process( make_and( ll, rr ), r, f ); } ),
                                make_or_actor( [&]( const auto & ll, const auto & rr )->ret_type
                                { return switch_process( make_or( ll, rr ), r, f ); } ),
                                make_not_actor(
                                    [&]( const auto & s ) { return switch_process( make_not( s ), r, f ); } ),
                                make_atomic_actor( [&]( const atomic_sentence & as )
                                { return switch_process( as, r, f ); } ) );
                };
        return self.template type_restore_full< ret_type >
                (
                    make_all_actor(
                        [&]( const variable & v, const auto & s )
                        { return make_all( v, move_quantifier_out( s ) ); } ),
                    make_some_actor(
                        [&]( const variable & v, const auto & s )
                        { return make_some( v, move_quantifier_out( s ) ); } ),
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
                            return move_quantifier_out( sen ).template type_restore_full< ret_type >(
                                        make_all_actor(
                                            [&]( const variable & v, const auto & s )
                                            {
                                                return
                                                    make_some(
                                                        v,
                                                        move_quantifier_out( make_not( ground_type( s ) ) ) );
                                            } ),
                                        make_some_actor(
                                            [&]( const variable & v, const auto & s )
                                            {
                                                return
                                                    make_all(
                                                        v,
                                                        move_quantifier_out( make_not( ground_type( s ) ) ) );
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
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    skolemization_remove_universal( const sentence< T > & self )
    {
        std::set< variable > s;
        return skolemization_remove_universal( self, s );
    }

    template< typename T, typename OUTITER >
    OUTITER used_name( const sentence< T > & self, OUTITER result )
    {
        return
            self.template type_restore_full< OUTITER >
            (
                make_all_actor(
                    [&]( const variable & v, const auto & s )
                    {
                        * result = v.name;
                        ++result;
                        return used_name( s, result );
                    } ),
                make_some_actor(
                    [&]( const variable & v, const auto & s )
                    {
                        * result = v.name;
                        ++result;
                        return used_name( s, result );
                    } ),
                make_or_actor( [&]( const auto & l, const auto & r ) { return used_name( l, used_name( r, result ) ); } ),
                make_and_actor( [&]( const auto & l, const auto & r ) { return used_name( l, used_name( r, result ) ); } ),
                make_not_actor( [&]( const auto & sen ) { return used_name( sen, result ); } ),
                make_atomic_actor( [&]( const atomic_sentence & sen ){ return used_name( sen, result ); } )
            );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    drop_existential( const sentence< T > & self )
    {
        return
            self.template type_restore_full
            <
                typename remove_operator
                <
                    sentence< T >,
                    set_c< sentence_type, sentence_type::some >
                >::type
            >(
                make_some_actor(
                    []( const variable &, const auto & se ) { return drop_existential( se ); } ),
                make_all_actor(
                    []( const variable & v, const auto & se ) { return make_all( v, drop_existential( se ) ); } ),
                make_atomic_actor( []( const atomic_sentence & as ) { return as; } ),
                make_and_actor(
                    []( const auto & l, const auto & r ) { return make_and( l.drop_existential( ), drop_existential( r ) ); } ),
                make_or_actor(
                    []( const auto & l, const auto & r ) { return make_or( l.drop_existential( ), r.drop_existential( ) ); } ),
                make_not_actor( []( const auto & s ) { return make_not_actor( s.drop_existential( ) ); } ) );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    drop_universal( const sentence< T > & self )
    {
        return
            self.template type_restore_full
            <
                typename remove_operator
                <
                    sentence< T >,
                    set_c< sentence_type, sentence_type::all >
                >::type
            >(
                make_all_actor(
                    []( const variable &, const auto & se ) { return drop_universal( se ); } ),
                make_some_actor(
                    []( const variable & v, const auto & se ) { return make_some( v, drop_universal( se ) ); } ),
                make_atomic_actor( []( const atomic_sentence & as ) { return as; } ),
                make_and_actor( []( const auto & l, const auto & r ) { return make_and( drop_universal( l ), drop_universal( r ) ); } ),
                make_or_actor( []( const auto & l, const auto & r ) { return make_or( drop_universal( l ), drop_universal( r ) ); } ),
                make_not_actor( []( const auto & s ) { return make_not( drop_universal( s ) ); } )
            );
    }

    template< typename T >
    typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    restore_quantifier_existential( const sentence< T > & self )
    {
        std::set< variable > var;
        free_variables( self, std::inserter( var, var.begin( ) ) );
        sentence< T > ret = self;
        for ( const variable & v : var ) { ret = make_some( v, ret ); }
        return ret;
    }

    template< typename T >
    typename add_sentence_front< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
    restore_quantifier_universal( const sentence< T > & self )
    {
        std::set< variable > var;
        free_variables( self, std::inserter( var, var.begin( ) ) );
        sentence< T > ret = self;
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
    sentence< T > standardize_bound_variable( const sentence< T > & self )
    {
        std::set< std::string > term_map;
        cv( make_function_output_iterator(
                [&]( const term & t )
                {
                    assert( t->term_type == term::type::constant || t->term_type == term::type::variable );
                    term_map.insert( t->name );
                } ) );
        return standardize_bound_variable( self, term_map );
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

    template< typename T, typename OUTITER >
    OUTITER cv( const sentence< T > & self, OUTITER result )
    {
        free_variables(
            self,
            constants( self, make_function_output_iterator( [&]( const auto & v ) { *result = term( v ); ++result; } ) ) );
        return result;
    }

    template< typename OUTITER >
    OUTITER constants( const atomic_sentence & self, OUTITER result )
    {
        return
                self.type_restore_full< OUTITER >(
                    make_equal_actor(
                        [&]( const term & l, const term & r )
                        { return l.constants( r.constants( result ) ); } ),
                    make_predicate_actor(
                        [&]( const std::string &, const std::vector< term > & vec )
                        {
                            for ( const term & t : vec )
                            { result = t.constants( result ); }
                            return result;
                        } ),
                    make_propositional_letter_actor(
                        [&]( const std::string & ) { return result; } ) );
    }
    template< typename OUTITER >
    OUTITER free_variables( const atomic_sentence & self, OUTITER result )
    {
        self.template type_restore_full< void >(
            make_equal_actor(
                [&]( const term & l, const term & r )
                { result = l.variables( r.variables( result ) ); } ),
            make_predicate_actor(
                [&]( const std::string &, const std::vector< term > & vec )
                { for ( const term & t : vec ) { result = t.variables( result ); } } ),
            make_propositional_letter_actor( []( const std::string & ){ } ) );
        return result;
    }
    template< typename OUTITER >
    OUTITER functions( const atomic_sentence & self, OUTITER result )
    {
        self.template type_restore_full< void >(
            make_equal_actor(
                [&]( const term & l, const term & r )
                { result = l.functions( r.functions( result ) ); } ),
            make_predicate_actor(
                [&]( const std::string &, const std::vector< term > & vec )
                { for ( const term & t : vec )
                { result = t.functions( result ); } } ),
            make_propositional_letter_actor( []( const std::string & ){ } ) );
        return result;
    }
    template< typename OUTITER >
    OUTITER used_name( const atomic_sentence & self, OUTITER result )
    {
        return self.template type_restore_full< OUTITER >(
            make_equal_actor(
                [&]( const term & l, const term & r )
                { return l.used_name( r.used_name( result ) ); } ),
            make_predicate_actor(
                [&]( const std::string & str, const std::vector< term > & vec )
                {
                    * result = str;
                    ++result;
                    for ( const term & t : vec )
                    { result = t.used_name( result ); }
                    return result;
                } ),
            make_propositional_letter_actor(
                [&]( const std::string & str )
                {
                    *result = str;
                    ++result;
                    return result;
                } ) );
     }
    template< typename OUTITER >
    OUTITER predicates( const atomic_sentence & self, OUTITER result )
    {
        self.template type_restore_full< void >(
            make_equal_actor( [&]( const term &, const term & ){ } ),
            make_predicate_actor(
                [&]( const std::string & str, const std::vector< term > & vec )
                {
                    *result = predicate( str, vec.size( ) );
                    ++result;
                } ),
            make_propositional_letter_actor( []( const std::string & ){ } ) );
        return result;
    }
    template< typename OUTITER >
    OUTITER cv( const atomic_sentence & self, OUTITER result )
    {
        free_variables( self,
            constants(
                self,
                make_function_output_iterator(
                    [&]( const auto & v ) { *result = term( v ); ++result; } ) ) );
        return result;
    }
}
#endif // SENTENCE_OPERATIONS_HPP
