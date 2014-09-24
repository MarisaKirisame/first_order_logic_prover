#ifndef IMPLEMENTATION_SENTENCE_HPP
#define IMPLEMENTATION_SENTENCE_HPP
#include "../sentence.hpp"
#include "substitution.hpp"
namespace first_order_logic
{
	inline sentence sentence::standardize_bound_variable( std::set< std::string > & term_map ) const
	{
		return
				type_restore_full
				(
					make_all_actor(
						[&]( const variable & v, const sentence & sen )
						{
							std::string gen_str = v.name;
							while ( term_map.count( gen_str ) != 0 ) { gen_str += "_"; }
							substitution sub( { std::make_pair( v, make_variable( gen_str ) ) } );
							return make_all( v, sub( sen ) );
						} ),
					make_some_actor(
						[&]( const variable & v, const sentence & sen )
						{
							std::string gen_str = v.name;
							while ( term_map.count( gen_str ) != 0 ) { gen_str += "_"; }
							substitution sub( { std::make_pair( v, make_variable( gen_str ) ) } );
							return make_some( v, sub( sen ) );
						} ),
					make_equal_actor( []( const term & l, const term & r ) { return make_equal( l, r ); } ),
					make_predicate_actor(
						[]( const std::string & str, const std::vector< term > & vec )
						{ return make_predicate( str, vec ); } ),
					make_propositional_letter_actor( []( const std::string & str ){ return make_propositional_letter( str ); } ),
					make_and_actor(
						[&]( const sentence & l, const sentence & r )
						{
							return make_and(
										l.standardize_bound_variable( term_map ),
										r.standardize_bound_variable( term_map ) );
						} ),
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							return make_or(
										l.standardize_bound_variable( term_map ),
										r.standardize_bound_variable( term_map ) );
						} ),
					make_not_actor
						( [&]( const sentence & s ){ return make_not( s.standardize_bound_variable( term_map ) ); } )
				);
	}
	inline sentence::operator std::string( ) const
	{
		if ( ! (*this)->cache.empty( ) ) { return (*this)->cache; }
		(*this)->cache =
				"(" +
				type_restore_full
				(
					make_and_actor(
						[&]( const sentence & l, const sentence & r )
						{
							return
								static_cast< std::string >( l ) +
								"/\\" +
								static_cast< std::string >( r );
						} ),
					make_some_actor(
						[&]( const variable & var, const sentence & sen )
						{
							return
								"∃" +
								var.name +
								" " +
								static_cast< std::string >( sen );
						} ),
					make_all_actor(
						[&]( const variable & var, const sentence & sen )
						{
							return
								"∀" +
								var.name +
								" " +
								static_cast< std::string >( sen );
						} ),
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							return
								static_cast< std::string >( l ) +
								"\\/" +
								static_cast< std::string >( r );
						} ),
					make_not_actor( [&]( const sentence & sen ){ return "!" + static_cast< std::string >( sen ); } ),
					make_equal_actor( [&]( const term & l, const term & r ){ return static_cast< std::string >( l ) + "=" + static_cast< std::string >( r ); } ),
					make_predicate_actor(
						[&]( const std::string & str, const std::vector< term > & vec )
						{
							std::string stack;
							auto it = vec.begin( );
							goto http;
							while ( it != vec.end( ) )
							{
								stack += ", ";
								http://marisa.moe
								stack += static_cast< std::string >( * it );
								++it;
							}
							return str + "(" + stack + ")";
						} ),
						make_propositional_letter_actor( [&]( const std::string & str ){ return str; } )
					) +
				")";
		return (*this)->cache;
	}
	inline size_t sentence::length( ) const
	{
		return
			type_restore_full
			(
				make_all_actor( []( const variable &, const sentence & s ){ return s.length( ); } ),
				make_some_actor( []( const variable &, const sentence & s ){ return s.length( ); } ),
				make_equal_actor( []( const term & l, const term & r ){ return l.length( ) + r.length( ); } ),
				make_predicate_actor( []( const std::string &, const std::vector< term > & )->size_t { return 0; } ),
				make_propositional_letter_actor( []( const std::string & )->size_t{ return 0; } ),
				make_and_actor( []( const sentence & l, const sentence & r ){ return l.length( ) + r.length( ); } ),
				make_or_actor( []( const sentence & l, const sentence & r ){ return l.length( ) + r.length( ); } ),
				make_not_actor( []( const sentence & sen ){ return sen.length( ); } )
			);
	}
	template< typename OUTITER >
	OUTITER sentence::functions( OUTITER result ) const
	{
		type_restore_full
		(
			make_all_actor( [&]( const variable &, const sentence & s ){ result = s.functions( result ); } ),
			make_some_actor( [&]( const variable &, const sentence & s ){ result = s.functions( result ); } ),
			make_equal_actor( [&]( const term & l, const term & r ) { result = l.functions( r.functions( result ) ); } ),
			make_predicate_actor( [&]( const std::string &, const std::vector< term > & vec ) { for ( const term & t : vec ) { result = t.functions( result ); } } ),
			make_propositional_letter_actor( []( const std::string & ){ } ),
			make_and_actor( [&]( const sentence & l, const sentence & r ) { result = l.functions( r.functions( result ) ); } ),
			make_or_actor( [&]( const sentence & l, const sentence & r ) { result = l.functions( r.functions( result ) ); } ),
			make_not_actor( [&]( const sentence & sen ){ result = sen.functions( result ); } )
		);
		return result;
	}
	template< typename OUTITER >
	OUTITER sentence::predicates( OUTITER result ) const
	{
		type_restore_full
		(
			make_all_actor( [&]( const variable &, const sentence & s ){ result = s.predicates( result ); } ),
			make_some_actor( [&]( const variable &, const sentence & s ){ result = s.predicates( result ); } ),
			make_equal_actor( [&]( const term &, const term & ){ } ),
			make_predicate_actor(
				[&]( const std::string & str, const std::vector< term > & vec )
				{
					*result = predicate( str, vec.size( ) );
					++result;
				} ),
			make_propositional_letter_actor( []( const std::string & ){ } ),
			make_and_actor( [&]( const sentence & l, const sentence & r ) { result = l.predicates( r.predicates( result ) ); } ),
			make_or_actor( [&]( const sentence & l, const sentence & r ) { result = l.predicates( r.predicates( result ) ); } ),
			make_not_actor( [&]( const sentence & sen ){ result = sen.predicates( result ); } )
		);
		return result;
	}
	template< typename OUTITER >
	OUTITER sentence::variables( OUTITER result ) const
	{
		type_restore_full
		(
			make_all_actor(
				[&]( const variable & var, const sentence & s )
				{
					*result = var;
					++result;
					result = s.variables( result );
				} ),
				make_some_actor(
				[&]( const variable & var, const sentence & s )
				{
					*result = var;
					++result;
					result = s.variables( result );
				} ),
				make_equal_actor( [&]( const term & l, const term & r ) { result = l.variables( r.variables( result ) ); } ),
				make_predicate_actor(
					[&]( const std::string &, const std::vector< term > & vec )
					{ for ( const term & t : vec ) { result = t.variables( result ); } } ),
				make_propositional_letter_actor( []( const std::string & ){ } ),
				make_and_actor(
					[&]( const sentence & l, const sentence & r ) { result = l.variables( r.variables( result ) ); } ),
				make_or_actor(
					[&]( const sentence & l, const sentence & r ) { result = l.variables( r.variables( result ) ); } ),
				make_not_actor( [&]( const sentence & sen ){ result = sen.variables( result ); } )
			);
		return result;
	}
	template< typename OUTITER >
	OUTITER sentence::bounded_variables( OUTITER result ) const
	{
		type_restore_full
		(
			make_all_actor(
				[&]( const variable & var, const sentence & s )
				{
					*result = var;
					++result;
					result = s.bounded_variables( result );
				} ),
				make_some_actor(
				[&]( const variable & var, const sentence & s )
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
					[&]( const sentence & l, const sentence & r )
					{ result = l.bounded_variables( r.bounded_variables( result ) ); } ),
				make_or_actor(
					[&]( const sentence & l, const sentence & r )
					{ result = l.bounded_variables( r.bounded_variables( result ) ); } ),
				make_not_actor( [&]( const sentence & sen ){ result = sen.bounded_variables( result ); } )
			);
		return result;
	}
	template< typename OUTITER >
	OUTITER sentence::free_variables( OUTITER result ) const
	{
		std::set< variable > bounded;
		bounded_variables( std::inserter( bounded, bounded.begin( ) ) );
		variables(
			make_function_output_iterator(
				[&]( const variable & v )
				{
					if ( bounded.count( v ) != 0 )
					{
						*result = v;
						++result;
					}
				} ) );
		return result;
	}
	inline bool sentence::have_equal( ) const
	{
		return
			type_restore_full
			(
				make_all_actor( [&]( const variable &, const sentence & s ) { return s.have_equal( ); } ),
				make_some_actor( [&]( const variable &, const sentence & s ) { return s.have_equal( ); } ),
				make_equal_actor( [&]( const term &, const term & ) { return true; } ),
				make_predicate_actor( [&]( const std::string &, const std::vector< term > & ){ return false; } ),
				make_propositional_letter_actor( []( const std::string & ) { return false; } ),
				make_and_actor( [&]( const sentence & l, const sentence & r ) { return l.have_equal( ) || r.have_equal( ); } ),
				make_or_actor( [&]( const sentence & l, const sentence & r ) { return l.have_equal( ) || r.have_equal( ); } ),
				make_not_actor( [&]( const sentence & sen ){ return sen.have_equal( ); } )
			);
	}
	template< typename OUTITER >
	OUTITER sentence::constants( OUTITER result ) const
	{
		return
			type_restore_full
			(
				make_all_actor( [&]( const variable &, const sentence & s ) { return s.constants( result ); } ),
				make_some_actor( [&]( const variable &, const sentence & s ) { return s.constants( result ); } ),
				make_equal_actor( [&]( const term & l, const term & r ) { return l.constants( r.constants( result ) ); } ),
				make_predicate_actor(
					[&]( const std::string &, const std::vector< term > & vec )
					{
						for ( const term & t : vec ) { result = t.constants( result ); }
						return result;
					} ),
				make_propositional_letter_actor( [&]( const std::string & ) { return result; } ),
				make_and_actor(
					[&]( const sentence & l, const sentence & r ) { return l.constants( r.constants( result ) ); } ),
				make_or_actor(
					[&]( const sentence & l, const sentence & r ) { return l.constants( r.constants( result ) ); } ),
				make_not_actor( [&]( const sentence & sen ){ return sen.constants( result ); } )
			);
	}
	inline bool sentence::have_quantifier( ) const
	{
		return
				type_restore_full
				(
					make_all_actor( []( const variable &, const sentence & ){ return true; } ),
					make_some_actor( []( const variable &, const sentence & ){ return true; } ),
					make_or_actor( []( const sentence & l, const sentence & r )
						{ return l.have_quantifier( ) || r.have_quantifier( ); } ),
					make_and_actor( []( const sentence & l, const sentence & r )
						{ return l.have_quantifier( ) || r.have_quantifier( ); } ),
					make_not_actor( []( const sentence & sen ){ return sen.have_quantifier( ); } ),
					make_equal_actor( []( const term &, const term & ){ return false; } ),
					make_predicate_actor( []( const std::string &, const std::vector< term > & ){ return false; } ),
					make_propositional_letter_actor( []( const std::string & ){ return false; } )
				);
	}
	inline bool sentence::is_in_prenex_form( ) const
	{
		return
				type_restore_full
				(
					make_all_actor( []( const variable &, const sentence &  sen ){ return sen.is_in_prenex_form( ); } ),
					make_some_actor( []( const variable &, const sentence & sen ){ return sen.is_in_prenex_form( ); } ),
					make_or_actor( []( const sentence & l, const sentence & r )
						{ return ( ! l.have_quantifier( ) ) && ( ! r.have_quantifier( ) ); } ),
					make_and_actor( []( const sentence & l, const sentence & r )
						{ return ( ! l.have_quantifier( ) ) && ( ! r.have_quantifier( ) ); } ),
					make_not_actor( []( const sentence & sen ){ return ! sen.have_quantifier( ); } ),
					make_equal_actor( []( const term &, const term & ){ return true; } ),
					make_predicate_actor( []( const std::string &, const std::vector< term > & ){ return true; } ),
					make_propositional_letter_actor( []( const std::string & ){ return true; } )
				);
	}
	inline sentence sentence::move_quantifier_out( ) const
	{
		return type_restore_full
				(
					make_all_actor( [&]( const variable & v, const sentence & s ) { return make_all( v, s.move_quantifier_out( ) ); } ),
					make_some_actor( [&]( const variable & v, const sentence & s ) { return make_some( v, s.move_quantifier_out( ) ); } ),
					make_equal_actor( [&]( const term & l, const term & r ) { return make_equal( l, r ); } ),
					make_predicate_actor( [&]( const std::string & str, const std::vector< term > & vec ) { return make_predicate( str, vec ); } ),
					make_propositional_letter_actor( [&]( const std::string & str ) { return make_propositional_letter( str ); } ),
					make_and_actor(
						[&]( const sentence & l, const sentence & r )
						{
							sentence ll = l.move_quantifier_out( );
							if ( ll->sentence_type == sentence::type::all || ll->sentence_type == sentence::type::some )
							{
								sentence ret;
								ll.type_restore(
									make_all_actor( [&]( const variable & v, const sentence & sen ) { ret = make_all( v, make_and( sen, r ) ); } ),
									make_some_actor( [&]( const variable & v, const sentence & sen ) { ret = make_some( v, make_and( sen, r ) ); } ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							sentence rr = r.move_quantifier_out( );
							if ( rr->sentence_type == sentence::type::all || rr->sentence_type == sentence::type::some )
							{
								sentence ret;
								rr.type_restore(
									make_all_actor( [&]( const variable & v, const sentence & sen ) { ret = make_all( v, make_and( l, sen ) ); } ),
									make_some_actor( [&]( const variable & v, const sentence & sen ) { ret = make_some( v, make_and( l, sen ) ); } ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							return make_and( l, r );
						} ),
					make_or_actor(
						[&]( const sentence & l, const sentence & r )
						{
							sentence ll = l.move_quantifier_out( );
							if ( ll->sentence_type == sentence::type::all || ll->sentence_type == sentence::type::some )
							{
								sentence ret;
								ll.type_restore(
									make_all_actor( [&]( const variable & v, const sentence & sen ) { ret = make_all( v, make_or( sen, r ) ); } ),
									make_some_actor( [&]( const variable & v, const sentence & sen ) { ret = make_some( v, make_or( sen, r ) ); } ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							sentence rr = r.move_quantifier_out( );
							if ( rr->sentence_type == sentence::type::all || rr->sentence_type == sentence::type::some )
							{
								sentence ret;
									rr.type_restore(
									make_all_actor( [&]( const variable & v, const sentence & sen ) { ret = make_all( v, make_or( l, sen ) ); } ),
									make_some_actor( [&]( const variable & v, const sentence & sen ) { ret = make_some( v, make_or( l, sen ) ); } ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							return make_or( l, r );
						} ),
						make_not_actor(
							[&]( const sentence & sen )
							{
								sentence ss = sen.move_quantifier_out( );
								if ( ss->sentence_type == sentence::type::all || ss->sentence_type == sentence::type::some )
								{
									sentence ret;
									ss.type_restore(
										make_all_actor( [&]( const variable & v, const sentence & sss ) { ret = make_some( v, sss ); } ),
										make_some_actor( [&]( const variable & v, const sentence & sss ) { ret = make_all( v, sss ); } ) );
									assert( ret.data );
									return ret.move_quantifier_out( );
								}
								return make_not( sen );
							} )
				);
	}

	inline sentence sentence::skolemization_remove_existential( ) const
	{
		if ( ! is_in_prenex_form( ) ) { return move_quantifier_out( ).skolemization_remove_existential( ); }
		std::set< variable > s;
		return skolemization_remove_existential( s );
	}

	inline sentence sentence::skolemization_remove_universal( ) const
	{
		if ( ! is_in_prenex_form( ) ) { return move_quantifier_out( ).skolemization_remove_universal( ); }
		std::set< variable > s;
		return skolemization_remove_universal( s );
	}

	inline sentence sentence::skolemization_remove_existential( std::set< variable > & previous_quantifier ) const
	{
		boost::optional< sentence > ret;
		type_restore
		(
			make_all_actor(
				[&]( const variable & v, const sentence & s )
				{
					previous_quantifier.insert( v );
					ret = make_all( v, s.skolemization_remove_existential( ) );
				} ),
			make_some_actor(
				[&]( const variable & v, const sentence & s )
				{
					if ( previous_quantifier.empty( ) )
					{
						std::set< std::string > used;
						cv( make_function_output_iterator( [&]( const term & t ){ used.insert( t->name ); } ) );
						std::string unused = "_";
						while ( used.count( unused ) != 0 ) { unused += "_"; }
						ret = substitution( { std::make_pair( v, make_variable( unused ) ) } )
								( s ).
								skolemization_remove_existential( );
					}
					else
					{
						std::set< std::string > fun;
						functions( make_function_output_iterator( [&]( const function & f ){ fun.insert( f.name ); } ) );
						std::string unused = "_";
						while ( fun.count( unused ) != 0 ) { unused += "_"; }
						ret = substitution( { std::make_pair( v, make_function( unused, std::vector< term >( previous_quantifier.begin( ), previous_quantifier.end( ) ) ) ) } )
								( s ).
								skolemization_remove_existential( );
					}
				} )
		);
		return ret ? * ret : * this;
	}

	inline sentence sentence::skolemization_remove_universal( std::set< variable > & previous_quantifier ) const
	{
		boost::optional< sentence > ret;
		type_restore
		(
			make_some_actor(
				[&]( const variable & v, const sentence & s )
				{
					previous_quantifier.insert( v );
					ret = make_some( v, s.skolemization_remove_existential( ) );
				} ),
			make_all_actor(
				[&]( const variable & v, const sentence & s )
				{
					if ( previous_quantifier.empty( ) )
					{
						std::set< std::string > used;
						cv( make_function_output_iterator( [&]( const term & t ){ used.insert( t->name ); } ) );
						std::string unused = "_";
						while ( used.count( unused ) != 0 ) { unused += "_"; }
						ret = substitution( { std::make_pair( v, make_variable( unused ) ) } )
								( s ).
								skolemization_remove_existential( );
					}
					else
					{
						std::set< std::string > fun;
						functions( make_function_output_iterator( [&]( const function & f ){ fun.insert( f.name ); } ) );
						std::string unused = "_";
						while ( fun.count( unused ) != 0 ) { unused += "_"; }
						ret = substitution( { std::make_pair( v, make_function( unused, std::vector< term >( previous_quantifier.begin( ), previous_quantifier.end( ) ) ) ) } )
								( s ).
								skolemization_remove_existential( );
					}
				} )
		);
		return ret ? * ret : * this;
	}

	inline sentence sentence::rectify( ) const
	{

	}

	inline sentence sentence::rectify( std::set< variable > & used_quantifier, std::set< std::string > & used_name ) const
	{

	}

	template< typename OUTITER >
	OUTITER sentence::used_name( OUTITER result ) const
	{
		return
				type_restore_full
				(
					make_all_actor(
						[&]( const variable & v, const sentence & s )
						{
							* result = v.name;
							++result;
							return s.used_name( result );
						} ),
					make_some_actor(
						[&]( const variable & v, const sentence & s )
						{
							* result = v.name;
							++result;
							return s.used_name( result );
						} ),
					make_or_actor( [&]( const sentence & l, const sentence & r )
						{ return l.used_name( r.used_name( result ) ); } ),
					make_and_actor( [&]( const sentence & l, const sentence & r )
						{ return l.used_name( r.used_name( result ) ); } ),
					make_not_actor( [&]( const sentence & sen ) { return sen.used_name( result ); } ),
					make_equal_actor(
						[&]( const term & l, const term & r ){ return l.used_name( r.used_name( result ) ); } ),
					make_predicate_actor(
						[&]( const std::string & str, const std::vector< term > & vec )
						{
							* result = str;
							++result;
							for ( const term & t : vec ) { result = t.used_name( result ); }
							return result;
						} ),
					make_propositional_letter_actor(
						[&]( const std::string & str )
						{
							*result = str;
							++result;
						} )
				);
	}
}
#endif // IMPLEMENTATION_SENTENCE_HPP
