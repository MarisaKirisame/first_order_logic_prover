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
        return rectify( self ).move_quantifier_out( ).template type_restore_full
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
                        self.cv( make_function_output_iterator(
                                [&]( const term & t ){ used.insert( t->name ); } ) );
                        std::string unused = "_";
                        while ( used.count( unused ) != 0 ) { unused += "_"; }
                        return skolemization_remove_existential( substitution( { std::make_pair( v, make_variable( unused ) ) } )( s ) );
                    }
                    else
                    {
                        std::set< std::string > fun;
                        self.functions( make_function_output_iterator(
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
        return self.rectify( ).move_quantifier_out( ).template type_restore_full
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
                            return make_all( v, s.skolemization_remove_universal( ) );
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
        std::set< std::string > used_name;
        std::set< variable > var;
        self.free_variables( std::inserter( var, var.begin( ) ) );
        self.used_name( std::inserter( used_name, used_name.begin( ) ) );
        return rectify( self, sv, var, used_name );
    }

    template< typename T >
    typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
    skolemization_remove_existential( const sentence< T > & self )
    {
        std::set< variable > s;
        return skolemization_remove_existential( self, s );
    }
}
#endif // SENTENCE_OPERATIONS_HPP
