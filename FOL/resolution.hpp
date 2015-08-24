#ifndef FIRST_ORDER_LOGIC_FOL_RESOLUTION_HPP
#define FIRST_ORDER_LOGIC_FOL_RESOLUTION_HPP
#include "sentence/sentence.hpp"
#include "sentence/term.hpp"
#include "TMP.hpp"
#include "sentence/sentence_operations.hpp"
#include "../cpp_common/iterator.hpp"
#include "sentence/CNF.hpp"
#include "satisfiability.hpp"
namespace first_order_logic
{
    satisfiability resolution( const free_propositional_sentence & sen )
    {
        auto CNF = set_set_literal( sen );
        std::set< std::set< literal > > to_be_added;
        bool have_new_inference = true;
        while ( have_new_inference )
        {
            have_new_inference = false;
            for ( const auto & l : CNF )
            {
                for ( const auto & r : CNF )
                {
                    if ( l != r )
                    {
                        for ( const literal & ll : l )
                        {
                            for ( const literal & rr : r )
                            {
                                if ( ll.b != rr.b )
                                {
                                    auto un = unify( ll.as, rr.as );
                                    if ( un )
                                    {
                                        std::set< literal > cl;
                                        for ( const literal & ins : l )
                                        {
                                            if ( (*un)( ins ) != (*un)( ll ) )
                                            { cl.insert( (*un)( ins ) ); }
                                        }
                                        for ( const literal & ins : r )
                                        {
                                            if ( (*un)( ins ) != (*un)( rr ) )
                                            { cl.insert( (*un)( ins ) ); }
                                        }
                                        if ( cl.empty( ) ) { return satisfiability::unsatisfiable; }
                                        to_be_added.insert( cl );
                                    }
                                }
                            }
                        }
                    }
                }
            }
            for ( const auto & clause : to_be_added )
            {
                if ( CNF.count( clause ) == 0 )
                {
                    CNF.insert( clause );
                    have_new_inference = true;
                }
            }
            to_be_added.clear( );
        }
        return satisfiability::satisfiable;
    }

    validity resolution( const free_sentence & sen, const free_sentence & goal )
    {
        return is_satisfiable( resolution( drop_universal( skolemization_remove_existential( move_quantifier_out( rectify(
                    make_and(
                        sen,
                        restore_quantifier_universal( make_not( goal ) ) ) ) ) ) ) ) ) ? validity::invalid : validity::valid;
    }
}
#endif //FIRST_ORDER_LOGIC_FOL_RESOLUTION_HPP
