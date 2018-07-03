//------------------------------------------------------------------------------
// GraphBLAS/Demo/bfs5m.c: breadth first search (mxv and assign/reduce)
//------------------------------------------------------------------------------

// Modified from the GraphBLAS C API Specification, 1.0.1, provisional release,
// by Aydin Buluc, Timothy Mattson, Scott McMillan, Jose' Moreira, Carl Yang.
// Based on "GraphBLAS Mathematics" by Jeremy Kepner.

// Modified further from above by Jenna Wise.
// *** JENNA CHANGE 6/21/18 ***
// Had to change all of the _Generic macro calls to their proper typed versions
// Frama-C does not support _Generic
// *** JENNA ANNOTATION 6/27/18 -- start of annotations ***

#include "demos.h"
#include "annotlib.acsl" // for useful common/factored out annotations

//------------------------------------------------------------------------------
// bfs5m: breadth first search using a Boolean semiring
//------------------------------------------------------------------------------

// Given a n x n adjacency matrix A and a source node s, performs a BFS
// traversal of the graph and sets v[i] to the level in which node i is
// visited (v[s] == 1).  If i is not reacheable from s, then v[i] = 0. (Vector
// v should be empty on input.)  The graph A need not be Boolean on input;
// if it isn't Boolean, the semiring will properly typecast it to Boolean.

// Annotations to be completed for bfs
/*@
 @ requires \valid(v_output);
 @ assigns *v_output;
 @ ensures \true;
 */
GrB_Info bfs5m              // BFS of a graph (using vector assign & reduce)
(
    GrB_Vector *v_output,   // v [i] is the BFS level of node i in the graph
    const GrB_Matrix A,     // input graph, treated as if boolean in semiring
    GrB_Index s             // starting node of the BFS
)
{

    //--------------------------------------------------------------------------
    // set up the semiring and initialize the vector v
    //--------------------------------------------------------------------------

    GrB_Info info ;
    GrB_Index n ;                          // # of nodes in the graph
    GrB_Vector q = NULL ;                  // nodes visited at each level
    GrB_Vector v = NULL ;                  // result vector
    GrB_Monoid Lor = NULL ;                // Logical-or monoid
    GrB_Semiring Boolean = NULL ;          // Boolean semiring
    GrB_Descriptor desc = NULL ;           // Descriptor for mxv

    GrB_Matrix_nrows (&n, A) ;             // n = # of rows of A
    GrB_Vector_new (&v, GrB_INT32, n) ;    // Vector<int32_t> v(n) = 0
    for (int32_t i = 0 ; i < n ; i++) GrB_Vector_setElement_INT32 (v, 0, i) ;
    GrB_Vector_new (&q, GrB_BOOL, n) ;     // Vector<bool> q(n) = false
    GrB_Vector_setElement_BOOL (q, true, s) ;   // q[s] = true, false elsewhere

    GrB_Monoid_new_BOOL (&Lor, GrB_LOR, (bool) false) ;
    GrB_Semiring_new (&Boolean, Lor, GrB_LAND) ;
    GrB_Descriptor_new (&desc) ;
    GrB_Descriptor_set (desc, GrB_MASK, GrB_SCMP) ;     // invert the mask
    GrB_Descriptor_set (desc, GrB_OUTP, GrB_REPLACE) ;  // clear q first

    //--------------------------------------------------------------------------
    // BFS traversal and label the nodes
    //--------------------------------------------------------------------------

    bool successor = true ; // true when some successor found
    for (int32_t level = 1 ; successor && level <= n ; level++)
    {
        // v<q> = level, using vector assign with q as the mask
        GrB_Vector_assign_INT32 (v, q, NULL, level, GrB_ALL, n, NULL) ;

        // q<!v> = A ||.&& q ; finds all the unvisited
        // successors from current q, using !v as the mask
        GrB_mxv (q, v, NULL, Boolean, A, q, desc) ;

        // successor = ||(q)
        GrB_Vector_reduce_BOOL (&successor, NULL, Lor, q, NULL) ;
    }

    *v_output = v ;         // return result

    GrB_Vector_free (&q) ;
    GrB_Monoid_free (&Lor) ;
    GrB_Semiring_free (&Boolean) ;
    GrB_Descriptor_free (&desc) ;

    return (GrB_SUCCESS) ;
}

