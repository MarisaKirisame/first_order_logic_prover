#ifndef FIRST_ORDER_LOGIC_FOL_PROOF_TREE_HPP
#define FIRST_ORDER_LOGIC_FOL_PROOF_TREE_HPP
#include <memory>
#include <string>
#include <vector>
namespace first_order_logic
{
    struct proof_tree
    {
        struct internal : std::enable_shared_from_this< internal >
        {
            virtual ~internal( ) { }
            internal * parent;
            std::string str;
            std::vector< proof_tree > child;
            internal( const std::string & str, const std::vector< proof_tree > & child = { } ) :
                internal( nullptr, str, child ) { }
            internal
            (
                internal * parent,
                const std::string & str,
                const std::vector< proof_tree > & child
            ) : parent( parent ), str( str ), child( child ) { }
            bool operator ==( const internal & comp ) const
            { return parent == comp.parent && str == comp.str && child == comp.child; }
            bool has_parent( ) const { return parent != nullptr; }
        };
        std::shared_ptr< internal > data;
        bool has_parent( ) const { return data && data->has_parent( ); }
        template< typename ... T >
        proof_tree( const T & ... t ) : data( new internal( t ... ) ) { }
        proof_tree( ) { }
        internal * operator ->( ) const { return data.get( ); }
        internal & operator * ( ) const { return * data; }
        bool operator == ( const proof_tree & comp ) const
        { return static_cast< bool >( data ) == static_cast< bool >( comp.data ) && * data == * comp.data; }
        proof_tree join( proof_tree child )
        {
            if ( data.get( ) == nullptr )
            {
                (*this) = child;
                return (*this);
            }
            child->parent = &**this;
            if ( child->str != (*this)->str )
            {
                (*this)->child.push_back( child );
                return child;
            }
            return (*this);
        }
    };
}
#endif //FIRST_ORDER_LOGIC_FOL_PROOF_TREE_HPP
