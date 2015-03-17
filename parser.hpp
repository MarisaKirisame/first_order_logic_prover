#ifndef FIRST_ORDER_LOGIC_PARSER_HPP
#define FIRST_ORDER_LOGIC_PARSER_HPP
#include "sentence.hpp"
#include "forward/first_order_logic.hpp"
#include <memory>
#define BOOST_SPIRIT_USE_PHOENIX_V3
#define BOOST_SPIRIT_UNICODE
#include <boost/spirit/include/qi.hpp>
#include <boost/spirit/include/phoenix_core.hpp>
#include <boost/spirit/include/phoenix_operator.hpp>
#include <boost/spirit/include/phoenix_fusion.hpp>
#include <boost/spirit/include/phoenix_stl.hpp>
#include <boost/fusion/include/adapt_struct.hpp>
#include <boost/phoenix/core/argument.hpp>
#include <boost/phoenix/function.hpp>
#include <boost/phoenix/bind.hpp>
#include <boost/spirit/include/qi_char_class.hpp>
#include <boost/phoenix/object/construct.hpp>
#include "variable.hpp"
namespace first_order_logic
{
    namespace
    {
        namespace spirit = boost::spirit;
        namespace qi = spirit::qi;
        namespace encoding  = boost::spirit::unicode;
        template< typename IT >
        struct FOL_grammar : qi::grammar< IT, boost::optional< free_sentence >( ), encoding::space_type >
        {
            FOL_grammar( ) : FOL_grammar::base_type( expression )
            {
                using qi::lit;
                using qi::lexeme;
                using encoding::char_;
                using encoding::string;
                using encoding::alnum;
                using encoding::alpha;
                using encoding::blank;
                using encoding::digit;
                using encoding::lower;
                using namespace qi::labels;
                namespace fusion = boost::fusion;
                namespace phoenix = boost::phoenix;
                namespace qi = boost::spirit::qi;
                namespace ascii = boost::spirit::ascii;
                using phoenix::at_c;
                using phoenix::push_back;
                using phoenix::bind;
                using phoenix::construct;
                text %= lexeme[alpha>>*(alnum)];
                parse_propositional_letter = text[ _val = bind( make_propositional_letter, _1 ) ];
                bool_exp =
                    ( lit( '(' ) >> expression >> lit( ')' ) ) [ _val = _1 ] |
                    with_equality [ _val = _1 ] |
                    predicate [ _val = _1 ] |
                    parse_propositional_letter [ _val = _1 ];
                with_equality =
                    ( term_exp >> lit( '=' ) >> term_exp )
                    [ bind( []( auto & val, auto & l, auto & r ) { val = make_equal( l, r ); }, _val, _1, _2 ) ];
                predicate =
                    ( text >> lit( '(' ) >> ( term_exp % ',' ) >> lit( ')' ) ) [ _val = bind( make_predicate, _1, _2 ) ];
                with_not =
                    bool_exp[ _val = _1 ] |
                        ( lit( '!' ) >> with_not )
                        [ bind( []( auto & val, auto & param ) { val = make_not( * param ); }, _val, _1 ) ];
                with_binary =
                    with_not[ _val = _1 ] >> *
                    (
                        ( lit( "/\\" ) >> with_not )
                            [ bind( []( auto & val, auto & param ) { val = make_and( * val, * param ); }, _val, _1 ) ] |
                        ( ( lit( "\\/" ) >> with_not )
                            [ bind( []( auto & val, auto & param ) { val = make_or( * val, * param ); }, _val, _1 ) ] )
                    );
                with_quantifier =
                    ( lit( u8"∃" ) >> parse_variable >> expression )
                        [ bind( []( auto & val, auto & param1, auto & param2 ) { val = make_some( param1, * param2 ); }, _val, _1, _2 ) ] |
                    ( lit( u8"∀" ) >> parse_variable >> expression )
                        [ bind( []( auto & val, auto & param1, auto & param2 ) { val = make_all( param1, * param2 ); }, _val, _1, _2 )] |
                with_binary[ _val = _1 ];
                with_implication =
                with_quantifier[ _val = _1 ] >> *
                (
                    ( lit( "->" ) >> with_quantifier )
                        [ bind( []( auto & val, auto & param ){ val = make_imply( * val, * param ); }, _val, _1 ) ] |
                    ( lit( "<-" ) >> with_quantifier )
                        [ bind( []( auto & val, auto & param ){ val = make_imply( * param, * val ); }, _val, _1 ) ] |
                    ( lit( "<->" ) >> with_quantifier )
                        [ bind( []( auto & val, auto & param ){ val = make_iff( * val, * param ); }, _val, _1 ) ]
                );
                expression %= with_implication;
                term_exp = function[ _val = _1 ] | text[ _val = bind( make_variable, _1 ) ];
                function =
                ( text >> lit( '(' ) >> ( term_exp % ',' ) >> lit( ')' ) )[ _val = bind( make_function, _1, _2 ) ];
                parse_variable = text[ _val = construct< variable >( _1 ) ];
            }
            qi::rule< IT, variable( ), encoding::space_type > parse_variable;
            qi::rule< IT, term( ), encoding::space_type >
                function,
                term_exp;
            qi::rule< IT, boost::optional< free_sentence >( ), encoding::space_type >
                with_equality,
                predicate,
                expression,
                bool_exp,
                with_not,
                with_binary,
                with_quantifier,
                parse_propositional_letter,
                with_implication;
            qi::rule< IT, std::string( ), encoding::space_type > text;
        };
    }
    boost::optional< free_sentence > parse( const std::string & s )
    {
        auto i = s.begin( );
        auto e = s.end( );
        boost::optional< free_sentence > ret;
        FOL_grammar< decltype( i ) > fol;
        bool succeed = boost::spirit::qi::phrase_parse( i, e, fol, boost::spirit::unicode::space, ret );
        if ( ! ( succeed && i == e ) ) { return boost::optional< free_sentence >( ); }
        return ret;
    }
}
#endif // FIRST_ORDER_LOGIC_PARSER_HPP
