#ifndef IMPLEMENTATION_SENTENCE_HPP
#define IMPLEMENTATION_SENTENCE_HPP
#include "../sentence.hpp"
#include "substitution.hpp"
#include "../../misc/expansion.hpp"
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
				make_and_actor(
						[]( const sentence< T > & l, const sentence< T > & r ){ return l.length( ) + r.length( ); } ),
				make_or_actor(
						[]( const sentence< T > & l, const sentence< T > & r ){ return l.length( ) + r.length( ); } ),
				make_not_actor(
						[]( const sentence< T > & sen ){ return sen.length( ); } )
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
				make_equal_actor(
					[&]( const term & l, const term & r ) { result = l.variables( r.variables( result ) ); } ),
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
			make_not_actor( [&]( const sentence< T > & sen ){ result = sen.bounded_variables( result ); } )
		);
		return result;
	}

	template< typename T >
	template< typename OUTITER >
	OUTITER sentence< T >::free_variables( OUTITER result ) const
	{
		return type_restore_full< OUTITER >
		(
			make_all_actor( [&]( const variable &, const sentence< T > & s ) { return s.free_variables( result ); } ),
			make_some_actor( [&]( const variable &, const sentence< T > & s ) { return s.free_variables( result ); } ),
			make_atomic_actor( [&]( const atomic_sentence & as ){ return as.free_variables( result ); } ),
			make_and_actor(
				[&]( const sentence< T > & l, const sentence< T > & r )
				{ return l.free_variables( r.free_variables( result ) ); } ),
			make_or_actor(
				[&]( const sentence< T > & l, const sentence< T > & r )
				{ return l.free_variables( r.free_variables( result ) ); } ),
			make_not_actor( [&]( const sentence< T > & sen ){ return sen.free_variables( result ); } )
		);
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
				make_all_actor( [&]( const variable &, const sentence< T > & s ) { return s.constants( result ); } ),
				make_some_actor( [&]( const variable &, const sentence< T > & s ) { return s.constants( result ); } ),
				make_atomic_actor( [&]( const atomic_sentence & as ){ return as.constants( result ); } ),
				make_and_actor(
					[&]( const sentence< T > & l, const sentence< T > & r )
					{ return l.constants( r.constants( result ) ); } ),
				make_or_actor(
					[&]( const sentence< T > & l, const sentence< T > & r )
					{ return l.constants( r.constants( result ) ); } ),
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
		auto switch_process =
				[]( const auto & processed, const auto & unprocessed, const auto & make )
				{
					typedef sentence< vector< typename all_sentence_operator< sentence< T > >::type > > ground_type;
					return unprocessed.move_quantifier_out( ).template type_restore_full< ret_type >(
								make_all_actor(
									[&]( const variable & v, const auto & s )
									{ return make_all( v, make( static_cast< ground_type >( s ), static_cast< ground_type >( processed ) ).move_quantifier_out( ) ); } ),
								make_some_actor(
									[&]( const variable & v, const auto & s )
									{ return make_some( v, make( static_cast< ground_type >( s ), static_cast< ground_type >( processed ) ).move_quantifier_out( ) ); } ),
								make_and_actor( [&]( const auto & l, const auto & r )->ret_type { return make( processed, make_and( l, r ) ); } ),
								make_or_actor( [&]( const auto & l, const auto & r )->ret_type { return make( processed, make_or( l, r ) ); } ),
								make_not_actor( [&]( const auto & s )->ret_type { return make( processed, make_not( s ) ); } ),
								make_atomic_actor( [&]( const atomic_sentence & as )->ret_type { return make( processed, as ); } ) );
				};
		auto do_process =
				[&]( const auto & l, const auto & r, const auto & f )
				{
					return l.move_quantifier_out( ).template type_restore_full< ret_type >(
								make_all_actor( [&]( const variable & v, const auto & s )->ret_type { return make_all( v, f( s, r ).move_quantifier_out( ) ); } ),
								make_some_actor( [&]( const variable & v, const auto & s )->ret_type { return make_some( v, f( s, r ).move_quantifier_out( ) ); } ),
								make_and_actor( [&]( const auto & ll, const auto & rr )->ret_type { return switch_process( make_and( ll, rr ), r, f ); } ),
								make_or_actor( [&]( const auto & ll, const auto & rr )->ret_type { return switch_process( make_or( ll, rr ), r, f ); } ),
								make_not_actor( [&]( const auto & s ) { return switch_process( make_not( s ), r, f ); } ),
								make_atomic_actor( [&]( const atomic_sentence & as ) { return switch_process( as, r, f ); } ) );
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
						[&]( const auto & l, const auto & r ) { return do_process( l, r, []( const auto & ll, const auto & rr ) { return make_and( ll, rr ); } ); } ),
					make_or_actor(
						[&]( const auto & l, const auto & r ) { return do_process( l, r, []( const auto & ll, const auto & rr ) { return make_or( ll, rr ); } ); } ),
					make_not_actor(
						[&]( const auto & sen )->ret_type
						{
							return sen.move_quantifier_out( ).template type_restore_full< ret_type >(
										make_all_actor( [&]( const variable & v, const auto & s )->ret_type { return make_some( v, s ); } ),
										make_some_actor( [&]( const variable & v, const auto & s )->ret_type { return make_all( v, s ); } ),
										make_and_actor( [&]( const auto & ll, const auto & rr )->ret_type { return make_not( make_and( ll, rr ) ); } ),
										make_or_actor( [&]( const auto & ll, const auto & rr )->ret_type { return make_not( make_or( ll, rr ) ); } ),
										make_not_actor( [&]( const auto & s ) { return s; } ),
										make_atomic_actor( [&]( const atomic_sentence & as ) { return make_not( as ); } ) );
						} )
				);
	}

	template< typename T >
	typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
	sentence< T >::skolemization_remove_existential( ) const
	{
		if ( ! is_in_prenex_form( ) ) { return move_quantifier_out( ).skolemization_remove_existential( ); }
		std::set< variable > s;
		return skolemization_remove_existential( s );
	}

	template< typename T >
	typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
	sentence< T >::skolemization_remove_universal( ) const
	{
		if ( ! is_in_prenex_form( ) ) { return move_quantifier_out( ).skolemization_remove_universal( ); }
		std::set< variable > s;
		return skolemization_remove_universal( s );
	}

	template< typename T >
	typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type
	sentence< T >::skolemization_remove_existential( std::set< variable > & previous_quantifier ) const
	{
		typedef
		typename remove_operator
		<
			sentence< T >,
			set_c< sentence_type, sentence_type::some >
		>::type ret_type;
		return rectify( ).move_quantifier_out( ).template type_restore_full
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
					return make_all( v, s.skolemization_remove_existential( ) );
				} ),
			make_some_actor(
				[&]( const variable & v, const auto & s )->ret_type
				{
					if ( previous_quantifier.empty( ) )
					{
						std::set< std::string > used;
						cv( make_function_output_iterator( [&]( const term & t ){ used.insert( t->name ); } ) );
						std::string unused = "_";
						while ( used.count( unused ) != 0 ) { unused += "_"; }
						return substitution( { std::make_pair( v, make_variable( unused ) ) } )
								( s ).
								skolemization_remove_existential( );
					}
					else
					{
						std::set< std::string > fun;
						functions( make_function_output_iterator( [&]( const function & f ){ fun.insert( f.name ); } ) );
						std::string unused = "_";
						while ( fun.count( unused ) != 0 ) { unused += "_"; }
						return substitution(
								{
									std::make_pair(
										v,
										make_function( unused, std::vector< term >( previous_quantifier.begin( ),
									previous_quantifier.end( ) ) ) )
								} )( s ).skolemization_remove_existential( );
					}
				} ),
			make_and_actor( []( const auto & l, const auto & r ) { return make_and( l, r ); } ),
			make_or_actor( []( const auto & l, const auto & r ) { return make_or( l, r ); } ),
			make_not_actor( [this]( const auto & l ) { return make_not( l ); } ),
			make_atomic_actor( []( const atomic_sentence & a ) { return a; } )
		);
	}
	template< typename T >
	typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
	sentence< T >::skolemization_remove_universal( std::set< variable > & previous_quantifier ) const
	{
		boost::optional< sentence< T > > ret;
		type_restore
		(
			make_some_actor(
				[&]( const variable & v, const sentence< T > & s )
				{
					previous_quantifier.insert( v );
					ret = make_some( v, s.skolemization_remove_universal( ) );
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
								skolemization_remove_universal( );
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
								} )( s ).skolemization_remove_universal( );
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
											substitution( { std::make_pair( v, make_variable( gen_str ) ) } )( sen ) );
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
					make_atomic_actor( [&]( const atomic_sentence & as )->sentence< T > { return sentence( as ); } ),
					make_or_actor(
						[&]( const auto & l, const auto & r )-> sentence< T >
						{
							return make_or(
									l.rectify( used_quantifier, free_variable, used_name ),
									r.rectify( used_quantifier, free_variable, used_name ) );
						} ),
					make_and_actor(
						[&]( const auto & l, const auto & r )-> sentence< T >
						{
							return make_and(
									l.rectify( used_quantifier, free_variable, used_name ),
									r.rectify( used_quantifier, free_variable, used_name ) );
						} ),
					make_not_actor(
						[&]( const auto & sen )-> sentence< T >
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
					typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::some > >::type >(
			make_some_actor( []( const variable &, const auto & se ) { return se.drop_existential( ); } ),
			make_all_actor(
				[]( const variable & v, const auto & se ) { return make_all( v, se.drop_existential( ) ); } ),
			make_atomic_actor( []( const atomic_sentence & as ) { return as; } ),
			make_and_actor(
				[]( const auto & l, const auto & r )
				{ return make_and( l.drop_existential( ), r.drop_existential( ) ); } ),
			make_or_actor(
				[]( const auto & l, const auto & r ) { return make_or( l.drop_existential( ), r.drop_existential( ) ); } ),
			make_not_actor( []( const auto & s ) { return make_not_actor( s.drop_existential( ) ); } ) );
	}
	template< typename T >
	typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type
	sentence< T >::drop_universal( ) const
	{
		return
				type_restore_full<
					typename remove_operator< sentence< T >, set_c< sentence_type, sentence_type::all > >::type >(
			make_all_actor( []( const variable &, const auto & se ) { return se.drop_universal( ); } ),
			make_some_actor(
				[]( const variable & v, const auto & se ) { return make_some( v, se.drop_universal( ) ); } ),
			make_atomic_actor( []( const atomic_sentence & as ) { return as; } ),
			make_and_actor(
				[]( const auto & l, const auto & r )
				{ return make_and( l.drop_universal( ), r.drop_universal( ) ); } ),
			make_or_actor(
				[]( const auto & l, const auto & r ) { return make_or( l.drop_universal( ), r.drop_universal( ) ); } ),
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
							[]( const std::false_type &, const auto &, const auto & ) { return error< RET >( )( ); },
							[&]( const std::true_type &, const auto & l, const auto & r ) { return and_func( l, r ); } )
						(
							have
							<
								typename current_set< sentence< T >  >::type,
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
				return misc::make_expansion(
							[]( const std::false_type &, const auto &, const auto & ) { return error< RET >( )( ); },
							[&]( const std::true_type &, const auto & l, const auto & r ) { return or_func( l, r ); } )
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
				return misc::make_expansion(
							[&]( const atomic_sentence & as ){ return atomic_func( as ); },
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
						( boost::get< typename next_sentence_type< sentence< T > >::type >( (*this)->arguments[0] ) );
		}
		throw std::invalid_argument( "unknown enum sentence_type" );
	}
	template< typename T >
	template< typename RET, typename ... ACTORS >
	RET sentence< T >::type_restore( const ACTORS & ... t ) const
	{
		return type_restore_inner< RET >(
			extract< and_actor_helper >(
				t ...,
				make_and_actor(
					std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
			extract< or_actor_helper >(
				t ...,
				make_or_actor(
					std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
			extract< not_actor_helper >(
				t ...,
				make_not_actor(
					std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
			extract< all_actor_helper >(
				t ...,
				make_all_actor(
					std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
			extract< some_actor_helper >(
				t ...,
				make_some_actor(
					std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ),
			extract< atomic_actor_helper >(
				t ...,
				make_atomic_actor(
					std::get< std::tuple_size< std::tuple< ACTORS ... > >::value - 1 >( std::tie( t ... ) ) ) ) );
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
					make_and_actor( []( const auto & l, const auto & r ) { return and_converter< TO >( )( l, r ); } ),
					make_or_actor( []( const auto & l, const auto & r ) { return or_converter< TO >( )( l, r ); } ),
					make_not_actor( []( const auto & t ) { return not_converter< TO >( )( t ); } ),
					make_all_actor( []( const variable & v, const auto & t ) { return all_converter< TO >( )( v, t ); } ),
					make_some_actor( []( const variable & v, const auto & t ) { return some_converter< TO >( )( v, t ); } ),
					make_atomic_actor( []( const atomic_sentence & as ) { return as; } ) );
	}
}
#endif // IMPLEMENTATION_SENTENCE_HPP
