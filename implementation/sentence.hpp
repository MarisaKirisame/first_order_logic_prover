#ifndef IMPLEMENTATION_SENTENCE_HPP
#define IMPLEMENTATION_SENTENCE_HPP
#include "../sentence.hpp"
#include "substitution.hpp"
namespace first_order_logic
{
	template< typename T >
	sentence< T > sentence< T >::standardize_bound_variable( std::set< std::string > & term_map ) const
	{
		return
				type_restore_full
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
					make_not_actor
						( [&]( const sentence< T > & s ){ return make_not( s.standardize_bound_variable( term_map ) ); } )
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
					make_not_actor( [&]( const sentence< T > & sen ){ return "!" + static_cast< std::string >( sen ); } ),
					make_atomic_actor( [&]( const atomic_sentence & as ){ return static_cast< std::string >( as ); } )
				) +
				")";
		return (*this)->cache;
	}
	template< typename T >
	size_t sentence< T >::length( ) const
	{
		return
			type_restore_full< size_t >
			(
				make_all_actor( []( const variable &, const sentence< T > & s ){ return s.length( ); } ),
				make_some_actor( []( const variable &, const sentence< T > & s ){ return s.length( ); } ),
				make_atomic_actor( []( const atomic_sentence & )->size_t{ return 0; } ),
				make_and_actor( []( const sentence< T > & l, const sentence< T > & r ){ return l.length( ) + r.length( ); } ),
				make_or_actor( []( const sentence< T > & l, const sentence< T > & r ){ return l.length( ) + r.length( ); } ),
				make_not_actor( []( const sentence< T > & sen ){ return sen.length( ); } )
			);
	}
	template< typename T >
	template< typename OUTITER >
	OUTITER sentence< T >::functions( OUTITER result ) const
	{
		type_restore_full< void >
		(
			make_all_actor( [&]( const variable &, const sentence< T > & s ){ result = s.functions( result ); } ),
			make_some_actor( [&]( const variable &, const sentence< T > & s ){ result = s.functions( result ); } ),
			make_atomic_actor( [&]( const atomic_sentence & as ){ result = as.functions( result ); } ),
			make_and_actor(
				[&]( const sentence< T > & l, const sentence< T > & r ) { result = l.functions( r.functions( result ) ); } ),
			make_or_actor(
				[&]( const sentence< T > & l, const sentence< T > & r ) { result = l.functions( r.functions( result ) ); } ),
			make_not_actor( [&]( const sentence< T > & sen ){ result = sen.functions( result ); } )
		);
		return result;
	}
	template< typename T >
	template< typename OUTITER >
	OUTITER sentence< T >::predicates( OUTITER result ) const
	{
		type_restore_full< void >
		(
			make_all_actor( [&]( const variable &, const sentence< T > & s ) { result = s.predicates( result ); } ),
			make_some_actor( [&]( const variable &, const sentence< T > & s ) { result = s.predicates( result ); } ),
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
				make_equal_actor( [&]( const term & l, const term & r ) { result = l.variables( r.variables( result ) ); } ),
				make_predicate_actor(
					[&]( const std::string &, const std::vector< term > & vec )
					{ for ( const term & t : vec ) { result = t.variables( result ); } } ),
				make_propositional_letter_actor( []( const std::string & ){ } ),
				make_and_actor(
					[&]( const sentence< T > & l, const sentence< T > & r ) { result = l.variables( r.variables( result ) ); } ),
				make_or_actor(
					[&]( const sentence< T > & l, const sentence< T > & r ) { result = l.variables( r.variables( result ) ); } ),
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
			make_not_actor( [&]( const sentence< T > & sen ){ result = sen.bounded_variables( result ); } )
		);
		return result;
	}
	template< typename T >
	template< typename OUTITER >
	OUTITER sentence< T >::free_variables( OUTITER result ) const
	{
		type_restore_full< void >
		(
			make_all_actor( [&]( const variable &, const sentence< T > & s ) { result = s.free_variables( result ); } ),
			make_some_actor( [&]( const variable &, const sentence< T > & s ) { result = s.free_variables( result ); } ),
			make_atomic_actor( [&]( const atomic_sentence & as ){ result = as.free_variables( result ); } ),
			make_and_actor(
				[&]( const sentence< T > & l, const sentence< T > & r )
				{ result = l.free_variables( r.free_variables( result ) ); } ),
			make_or_actor(
				[&]( const sentence< T > & l, const sentence< T > & r )
				{ result = l.free_variables( r.free_variables( result ) ); } ),
			make_not_actor( [&]( const sentence< T > & sen ){ result = sen.free_variables( result ); } )
		);
		return result;
	}
	template< typename T >
	bool sentence< T >::have_equal( ) const
	{
		return
			type_restore_full< bool >
			(
				make_all_actor( [&]( const variable &, const sentence< T > & s ) { return s.have_equal( ); } ),
				make_some_actor( [&]( const variable &, const sentence< T > & s ) { return s.have_equal( ); } ),
				make_atomic_actor(
						[&]( const atomic_sentence & as )
						{ return as->atomic_sentence_type == atomic_sentence::type::equal; } ),
				make_and_actor(
						[&]( const sentence< T > & l, const sentence< T > & r ) { return l.have_equal( ) || r.have_equal( ); } ),
				make_or_actor(
						[&]( const sentence< T > & l, const sentence< T > & r ) { return l.have_equal( ) || r.have_equal( ); } ),
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
				make_all_actor( [&]( const variable &, const sentence< T > & s ) { return s.constants( result ); } ),
				make_some_actor( [&]( const variable &, const sentence< T > & s ) { return s.constants( result ); } ),
				make_atomic_actor( [&]( const atomic_sentence & as ){ return as.constants( result ); } ),
				make_and_actor(
					[&]( const sentence< T > & l, const sentence< T > & r ) { return l.constants( r.constants( result ) ); } ),
				make_or_actor(
					[&]( const sentence< T > & l, const sentence< T > & r ) { return l.constants( r.constants( result ) ); } ),
				make_not_actor( [&]( const sentence< T > & sen ){ return sen.constants( result ); } )
			);
	}
	template< typename T >
	bool sentence< T >::have_quantifier( ) const
	{
		return
				type_restore_full< bool >
				(
					make_all_actor( []( const variable &, const sentence< T > & ){ return true; } ),
					make_some_actor( []( const variable &, const sentence< T > & ){ return true; } ),
					make_or_actor( []( const sentence< T > & l, const sentence< T > & r )
						{ return l.have_quantifier( ) || r.have_quantifier( ); } ),
					make_and_actor( []( const sentence< T > & l, const sentence< T > & r )
						{ return l.have_quantifier( ) || r.have_quantifier( ); } ),
					make_not_actor( []( const sentence< T > & sen ){ return sen.have_quantifier( ); } ),
					make_atomic_actor( []( const atomic_sentence & ){ return false; } )
				);
	}
	template< typename T >
	bool sentence< T >::is_in_prenex_form( ) const
	{
		return
				type_restore_full< bool >
				(
					make_all_actor( []( const variable &, const sentence< T > &  sen ){ return sen.is_in_prenex_form( ); } ),
					make_some_actor( []( const variable &, const sentence< T > & sen ){ return sen.is_in_prenex_form( ); } ),
					make_or_actor( []( const sentence< T > & l, const sentence< T > & r )
						{ return ( ! l.have_quantifier( ) ) && ( ! r.have_quantifier( ) ); } ),
					make_and_actor( []( const sentence< T > & l, const sentence< T > & r )
						{ return ( ! l.have_quantifier( ) ) && ( ! r.have_quantifier( ) ); } ),
					make_not_actor( []( const sentence< T > & sen ){ return ! sen.have_quantifier( ); } ),
					make_atomic_actor( []( const atomic_sentence & ){ return true; } )
				);
	}
	template< typename T >
	sentence< T > sentence< T >::move_quantifier_out( ) const
	{
		return type_restore_full< sentence< T > >
				(
					make_all_actor(
						[&]( const variable & v, const sentence< T > & s )
						{ return make_all( v, s.move_quantifier_out( ) ); } ),
					make_some_actor(
						[&]( const variable & v, const sentence< T > & s )
						{ return make_some( v, s.move_quantifier_out( ) ); } ),
					make_atomic_actor( []( const atomic_sentence & as ){ return sentence( as ); } ),
					make_and_actor(
						[&]( const sentence< T > & l, const sentence< T > & r )
						{
							sentence< T > ll = l.move_quantifier_out( );
							if ( ll->type == sentence_type::all || ll->type == sentence_type::some )
							{
								sentence< T > ret;
								ll.type_restore< void >(
									make_all_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_all( v, make_and( sen, r ) ); } ),
									make_some_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_some( v, make_and( sen, r ) ); } ),
									error< >( ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							sentence< T > rr = r.move_quantifier_out( );
							if ( rr->type == sentence_type::all || rr->type == sentence_type::some )
							{
								sentence< T > ret;
								rr.type_restore< void >(
									make_all_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_all( v, make_and( l, sen ) ); } ),
									make_some_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_some( v, make_and( l, sen ) ); } ),
									error< >( ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							return make_and( l, r );
						} ),
					make_or_actor(
						[&]( const sentence< T > & l, const sentence< T > & r )
						{
							sentence< T > ll = l.move_quantifier_out( );
							if ( ll->type == sentence_type::all || ll->type == sentence_type::some )
							{
								sentence< T > ret;
								ll.type_restore< void >(
									make_all_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_all( v, make_or( sen, r ) ); } ),
									make_some_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_some( v, make_or( sen, r ) ); } ),
									error< >( ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							sentence< T > rr = r.move_quantifier_out( );
							if ( rr->type == sentence_type::all || rr->type == sentence_type::some )
							{
								sentence< T > ret;
									rr.type_restore< void >(
									make_all_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_all( v, make_or( l, sen ) ); } ),
									make_some_actor(
										[&]( const variable & v, const sentence< T > & sen )
										{ ret = make_some( v, make_or( l, sen ) ); } ),
									error< >( ) );
								assert( ret.data );
								return ret.move_quantifier_out( );
							}
							return make_or( l, r );
						} ),
						make_not_actor(
							[&]( const sentence< T > & sen )
							{
								sentence< T > ss = sen.move_quantifier_out( );
								if (
										ss->type == sentence_type::all ||
										ss->type == sentence_type::some )
								{
									sentence< T > ret;
									ss.type_restore< void >(
										make_all_actor(
											[&]( const variable & v, const sentence< T > & sss )
											{ ret = make_some( v, sss ); } ),
										make_some_actor(
											[&]( const variable & v, const sentence< T > & sss )
											{ ret = make_all( v, sss ); } ),
										error< >( ) );
									assert( ret.data );
									return ret.move_quantifier_out( );
								}
								return make_not( sen );
							} )
				);
	}
	template< typename T >
	sentence< T > sentence< T >::skolemization_remove_existential( ) const
	{
		if ( ! is_in_prenex_form( ) ) { return move_quantifier_out( ).skolemization_remove_existential( ); }
		std::set< variable > s;
		return skolemization_remove_existential( s );
	}
	template< typename T >
	sentence< T > sentence< T >::skolemization_remove_universal( ) const
	{
		if ( ! is_in_prenex_form( ) ) { return move_quantifier_out( ).skolemization_remove_universal( ); }
		std::set< variable > s;
		return skolemization_remove_universal( s );
	}
	template< typename T >
	sentence< T > sentence< T >::skolemization_remove_existential( std::set< variable > & previous_quantifier ) const
	{
		boost::optional< sentence< T > > ret;
		type_restore< void >
		(
			make_all_actor(
				[&]( const variable & v, const sentence< T > & s )
				{
					previous_quantifier.insert( v );
					ret = make_all( v, s.skolemization_remove_existential( ) );
				} ),
			make_some_actor(
				[&]( const variable & v, const sentence< T > & s )
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
						ret = substitution(
								{
									std::make_pair(
										v,
										make_function( unused, std::vector< term >( previous_quantifier.begin( ),
									previous_quantifier.end( ) ) ) )
								} )( s ).skolemization_remove_existential( );
					}
				} ),
			ignore< >( )
		);
		return ret ? * ret : * this;
	}
	template< typename T >
	sentence< T > sentence< T >::skolemization_remove_universal( std::set< variable > & previous_quantifier ) const
	{
		boost::optional< sentence< T > > ret;
		type_restore
		(
			make_some_actor(
				[&]( const variable & v, const sentence< T > & s )
				{
					previous_quantifier.insert( v );
					ret = make_some( v, s.skolemization_remove_existential( ) );
				} ),
			make_all_actor(
				[&]( const variable & v, const sentence< T > & s )
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
						ret =
								substitution(
								{
									std::make_pair(
										v,
										make_function(
											unused,
											std::vector< term >( previous_quantifier.begin( ),
										previous_quantifier.end( ) ) ) )
								} )( s ).skolemization_remove_existential( );
					}
				} ),
			error< >( )
		);
		return ret ? * ret : * this;
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
	sentence< T > sentence< T >::rectify(
		std::set< variable > & used_quantifier,
		const std::set< variable > & free_variable,
		std::set< std::string > & used_name ) const
	{
		return type_restore_full< sentence< T > >
				(
					make_all_actor(
						[&]( const variable & v, const sentence< T > & sen )
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
											substitution( { std::make_pair( v, make_variable( gen_str ) ) } )( sen ) );
							}
							return make_all( v, sen );
						} ),
					make_some_actor(
						[&]( const variable & v, const sentence< T > & sen )
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
					make_atomic_actor( [&]( const atomic_sentence & as ){ return sentence( as ); } ),
					make_or_actor(
						[&]( const sentence< T > & l, const sentence< T > & r )
						{
							return make_or(
									l.rectify( used_quantifier, free_variable, used_name ),
									r.rectify( used_quantifier, free_variable, used_name ) );
						} ),
					make_and_actor(
						[&]( const sentence< T > & l, const sentence< T > & r )
						{
							return make_and(
									l.rectify( used_quantifier, free_variable, used_name ),
									r.rectify( used_quantifier, free_variable, used_name ) );
						} ),
					make_not_actor(
						[&]( const sentence< T > & sen )
						{ return make_not( sen.rectify( used_quantifier, free_variable, used_name ) ); } )
				);
	}
	template< typename T >
	template< typename OUTITER >
	OUTITER sentence< T >::used_name( OUTITER result ) const
	{
		return
				type_restore_full< OUTITER >
				(
					make_all_actor(
						[&]( const variable & v, const sentence< T > & s )
						{
							* result = v.name;
							++result;
							return s.used_name( result );
						} ),
					make_some_actor(
						[&]( const variable & v, const sentence< T > & s )
						{
							* result = v.name;
							++result;
							return s.used_name( result );
						} ),
					make_or_actor( [&]( const sentence< T > & l, const sentence< T > & r )
						{ return l.used_name( r.used_name( result ) ); } ),
					make_and_actor( [&]( const sentence< T > & l, const sentence< T > & r )
						{ return l.used_name( r.used_name( result ) ); } ),
					make_not_actor( [&]( const sentence< T > & sen ) { return sen.used_name( result ); } ),
					make_atomic_actor( [&]( const atomic_sentence & sen ){ return sen.used_name( result ); } )
				);
	}
	template< typename T >
	sentence< T > sentence< T >::drop_existential( ) const
	{
		boost::optional< sentence< T > > sen;
		type_restore(
			make_some_actor( [&]( const variable &, const sentence< T > & se ){ sen = se.drop_existential( ); } ),
			ignore< >( ) );
		return sen ? * sen : * this;
	}
	template< typename T >
	sentence< T > sentence< T >::drop_universal( ) const
	{
		boost::optional< sentence< T > > sen;
		type_restore< void >(
			make_all_actor( [&]( const variable &, const sentence< T > & se ){ sen = se.drop_universal( ); } ),
			ignore< >( ) );
		return sen ? * sen : * this;
	}
	template< typename T >
	sentence< T > sentence< T >::restore_quantifier_existential( ) const
	{
		std::set< variable > var;
		free_variables( std::inserter( var, var.begin( ) ) );
		sentence< T > ret = * this;
		for ( const variable & v : var ) { ret = make_some( v, ret ); }
		return ret;
	}
	template< typename T >
	sentence< T > sentence< T >::restore_quantifier_universal( ) const
	{
		std::set< variable > var;
		free_variables( std::inserter( var, var.begin( ) ) );
		sentence< T > ret = * this;
		for ( const variable & v : var ) { ret = make_all( v, ret ); }
		return ret;
	}
}
#endif // IMPLEMENTATION_SENTENCE_HPP
