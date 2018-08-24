//------------------------------------------------------------------------------
// GB_free_pending: free all pending tuples
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 7/28/18 ***
// GB_free_pending

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires (matrix_valid(A) ||
           matrix_malloc_valid(A)) ;
 requires (A->ipending != \null ==> \freeable(A->ipending)) ;
 requires (A->jpending != \null ==> \freeable(A->jpending)) ;
 requires (A->xpending != \null ==> \freeable(A->xpending)) ;
 
 frees A->ipending ;
 frees A->jpending ;
 frees A->xpending ;
 
 assigns __fc_heap_status ;
 
 assigns A->ipending ;
 assigns A->jpending ;
 assigns A->xpending ;
 assigns A->npending ;
 assigns A->max_npending ;
 assigns A->sorted_pending ;
 assigns A->operator_pending ;
 
 ensures A->ipending == \null ;
 ensures A->jpending == \null ;
 ensures A->xpending == \null ;
 ensures A->npending == 0 ;
 ensures A->max_npending == 0 ;
 ensures A->sorted_pending == 1 ;
 ensures A->operator_pending == \null ;
 
 // undefined behavior if not valid matrix
 //behavior matrix_invalid :
 //   assumes !matrix_valid(A) ;
 //   assumes !matrix_malloc_valid(A) ;
 //   ensures \true ;
 
 behavior matrix_malloc_valid :
    assumes matrix_malloc_valid(A) ;
    ensures matrix_malloc_valid(A) ;
 
 behavior matrix_valid :
    assumes matrix_valid(A) ;
    ensures matrix_valid(A) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
void GB_free_pending            // free all pending tuples
(
    GrB_Matrix A                // matrix with pending tuples to free
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    ASSERT (A != NULL) ;

    //--------------------------------------------------------------------------
    // free all pending tuples
    //--------------------------------------------------------------------------

    GB_FREE_MEMORY (A->ipending, A->max_npending, sizeof (int64_t)) ;
    GB_FREE_MEMORY (A->jpending, A->max_npending, sizeof (int64_t)) ;
    GB_FREE_MEMORY (A->xpending, A->max_npending, A->type->size) ;
    A->npending = 0 ;
    A->max_npending = 0 ;
    A->sorted_pending = true ;
    A->operator_pending = NULL ;
}

