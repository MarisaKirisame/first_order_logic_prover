#ifndef THEOREM_PROVER_FIRST_ORDER_LOGIC_PRASER_HPP
#define THEOREM_PROVER_FIRST_ORDER_LOGIC_PRASER_HPP
#include "term.hpp"
#include "first_order_logic.hpp"
#include <memory>
#define BOOST_SPIRIT_USE_PHOENIX_V3
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
			namespace ascii = spirit::ascii;
			template< typename IT >
			struct FOL_grammar : qi::grammar< IT, std::shared_ptr< term >( ), ascii::space_type >
			{
				FOL_grammar( ) : FOL_grammar::base_type( expression )
				{
					using qi::lit;
					using qi::lexeme;
					using ascii::char_;
					using ascii::string;
					using boost::spirit::ascii::alnum;
					using boost::spirit::ascii::alpha;
					using boost::spirit::ascii::blank;
					using boost::spirit::ascii::digit;
					using boost::spirit::ascii::lower;
					using namespace qi::labels;
					namespace fusion = boost::fusion;
					namespace phoenix = boost::phoenix;
					namespace qi = boost::spirit::qi;
					namespace ascii = boost::spirit::ascii;
					using phoenix::at_c;
					using phoenix::push_back;
					using phoenix::bind;
					text %= lexeme[alpha>>*(alnum)];
					variable = text[ _val = bind( make_variable, _1 ) ];
					with_not =
										 variable[ _val = _1 ] |
										 ( lit( '!' ) >> with_not )[ _val = bind( make_not, _1 ) ];
					with_binary =
										 with_not[ _val = _1 ] >> *
										 (
											( lit( "/\\" ) >> with_not )[ _val = bind( make_and, _1, _val ) ] |
											 ( lit( "\\/" ) >> with_not )[ _val = bind( make_or, _1, _val ) ] );
					with_quantifier %= with_binary;
					with_implication = with_quantifier[ _val = _1 ] >> *
										 (
											( lit( "->" ) >> with_not )[ _val = bind( make_imply, _1, _val ) ] |
											 ( lit( "<-" ) >> with_not )[ _val = bind( make_imply, _val, _1 ) ] |
											 ( lit( "<->" ) >> with_not )[ _val = bind( make_iff, _1, _val ) ] );
					expression %= with_implication;
				}
				qi::rule< IT, std::shared_ptr< term >( ), ascii::space_type >
										 expression,
										 variable,
										 with_not,
										 with_binary,
										 with_quantifier,
										 with_implication;
				qi::rule< IT, std::string( ), ascii::space_type> text;
			};
		}
		template< typename STR >
		std::shared_ptr< term > prase( const STR & s )
		{
			auto i = s.begin( );
			auto e = s.end( );
			std::shared_ptr< term > ret;
			FOL_grammar< decltype( i ) > fol;
			bool succeed = boost::spirit::qi::phrase_parse( i, e, fol, boost::spirit::ascii::space, ret );
			assert( succeed && i == e );
			return ret;
		}
	}
}
#endif // PRASER_HPP
