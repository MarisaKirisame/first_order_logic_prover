#ifndef RESOLUTION_HPP
#define RESOLUTION_HPP
#include <boost/optional/optional.hpp>
#include "sentence.hpp"
#include "term.hpp"
#include "TMP.hpp"
#include "sentence_operations.hpp"
#include "../cpp_common/iterator.hpp"
#include "CNF.hpp"
namespace first_order_logic
{
    bool resolution( const free_propositional_sentence & sen )
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
                                            if ( (*un)( ins.as ) != (*un)( ll.as ) )
                                            { cl.insert( literal( (*un)( ins.as ), ins.b ) ); }
                                        }
                                        for ( const literal & ins : r )
                                        {
                                            if ( (*un)( ins.as ) != (*un)( rr.as ) )
                                            { cl.insert( literal( (*un)( ins.as ), ins.b ) ); }
                                        }
                                        if ( cl.empty( ) ) { return false; }
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
        return true;
    }

    bool resolution( const free_sentence & sen, const free_sentence & goal )
    {
        return ! resolution(
                    drop_universal(
                        skolemization_remove_existential(
                            move_quantifier_out(
                                rectify(
                                    make_and(
                                        sen,
                                        restore_quantifier_universal( make_not( goal ) ) ) ) ) ) ) );
    }
}
#endif // RESOLUTION_HPP
