#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_PRASER_HPP
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_PRASER_HPP
#include "term.hpp"
#include "first_order_logic.hpp"
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
namespace theorem_prover
{
	namespace first_order_logic
	{
		namespace
		{
			namespace spirit = boost::spirit;
			namespace qi = spirit::qi;
			namespace encoding  = boost::spirit::unicode;
			template< typename IT >
			struct FOL_grammar : qi::grammar< IT, std::shared_ptr< term >( ), encoding::space_type >
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
					text %= lexeme[alpha>>*(alnum)];
					bool_exp %= ( lit( '(' ) >> expression >> lit( ')' ) ) | with_equality | predicate | variable;
					with_equality = ( term_exp >> lit( '=' ) >> term_exp )[ _val = bind( make_equal, _1, _2 ) ];
					predicate = ( text >> lit( '(' ) >> ( term_exp % ',' ) >> lit( ')' ) )[ _val = bind( make_predicate, _1, _2 ) ];
					with_not =
										 bool_exp[ _val = _1 ] |
										 ( lit( '!' ) >> with_not )[ _val = bind( make_not, _1 ) ];
					with_binary =
										 with_not[ _val = _1 ] >> *
										 (
											( lit( "/\\" ) >> with_not )[ _val = bind( make_and, _1, _val ) ] |
											 ( lit( "\\/" ) >> with_not )[ _val = bind( make_or, _1, _val ) ] );
					with_quantifier %= with_binary;
					with_implication =
										 with_quantifier[ _val = _1 ] >> *
										 (
											( lit( "->" ) >> with_not )[ _val = bind( make_imply, _1, _val ) ] |
											 ( lit( "<-" ) >> with_not )[ _val = bind( make_imply, _val, _1 ) ] |
											 ( lit( "<->" ) >> with_not )[ _val = bind( make_iff, _1, _val ) ] );
					expression =
													( lit( "∃" ) >> text >> expression )[ _val = bind( make_some, _1, _2 ) ] |
													( lit( "∀" ) >> text >> expression )[ _val = bind( make_all, _1, _2 ) ] |
													with_implication[ _val = _1 ];
					term_exp = function[ _val = _1 ] | text[ _val = bind( make_variable, _1 ) ];
					function = ( text >> lit( '(' ) >> ( term_exp % ',' ) >> lit( ')' ) )[ _val = bind( make_function, _1, _2 ) ];
					variable = text[ _val = bind( make_variable, _1 ) ];
				}
				qi::rule< IT, std::shared_ptr< term >( ), encoding::space_type >
										 term_exp,
										 variable,
										 with_equality,
										 predicate,
										 function,
										 expression,
										 bool_exp,
										 with_not,
										 with_binary,
										 with_quantifier,
										 with_implication;
				qi::rule< IT, std::string( ), encoding::space_type> text;
			};
		}
		std::shared_ptr< term > prase( const std::string & s )
		{
			auto i = s.begin( );
			auto e = s.end( );
			std::shared_ptr< term > ret;
			FOL_grammar< decltype( i ) > fol;
			bool succeed = boost::spirit::qi::phrase_parse( i, e, fol, boost::spirit::unicode::space, ret );
			assert( succeed && i == e );
			return ret;
		}
	}
}
#endif // PRASER_HPP
