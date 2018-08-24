//------------------------------------------------------------------------------
// GrB_Matrix_clear: clears the content of a matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/24/18 ***
// GrB_Matrix_clear

//------------------------------------------------------------------------------

// The A->x and A->i content is freed and the column pointers A->p are set to
// zero.  This puts the matrix A in the same state it had after GrB_Matrix_new
// (&A, ...).  The dimensions and type of A are not changed.  To change the
// size or type requires a GrB_Matrix_free (&A) followed by another call to
// GrB_Matrix_new (&A, ...) with the new dimensions and type.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires (A != \null ==> \valid(A)) ;
 requires (A != \null && matrix_init(A) ==>
            matrix_valid(A) &&
            A->p_shallow == 0 &&
            freeable_storage(A)) ;
 
 requires \separated(&GB_thread_local,A) ;
 requires (GB_thread_local.where != \null || A != \null) ==>
            \separated(GB_thread_local.where,A) ;
 requires (GB_thread_local.file != \null || A != \null) ==>
            \separated(GB_thread_local.file,A) ;
 
 frees A->i ;
 frees A->x ;
 frees A->ipending ;
 frees A->jpending ;
 frees A->xpending ;
 
 assigns __fc_heap_status ;
 
 assigns GB_thread_local.where ;
 assigns GB_thread_local.file ;
 assigns GB_thread_local.line ;
 assigns GB_thread_local.info ;
 
 assigns A->magic ;
 assigns (A->p)[0..matrix_ncols(A)] ;
 assigns A->i ;
 assigns A->i_shallow ;
 assigns A->x ;
 assigns A->x_shallow ;
 assigns A->nzmax ;
 assigns A->nzombies ;
 
 assigns A->ipending ;
 assigns A->jpending ;
 assigns A->xpending ;
 assigns A->npending ;
 assigns A->max_npending ;
 assigns A->sorted_pending ;
 assigns A->operator_pending ;
 
 assigns A->queue_prev ;
 assigns A->queue_next ;
 assigns A->enqueued ;
 
 ensures \result == GrB_SUCCESS              ||
         \result == GrB_NULL_POINTER         ||
         \result == GrB_INVALID_OBJECT       ||
         \result == GrB_UNINITIALIZED_OBJECT ||
         \result == GrB_PANIC ;
 
 behavior matrix_null :
    assumes A == \null ;
    ensures \result == GrB_NULL_POINTER ==> A == \null ;
 
 behavior matrix_invalid :
    assumes A != \null ;
    assumes !matrix_valid(A) ;
 
    requires \valid(A) ;
 
    ensures (\result == GrB_INVALID_OBJECT ==>
                !matrix_valid(A))                    ||
            (\result == GrB_UNINITIALIZED_OBJECT ==>
                \valid(A) &&
                !matrix_init(A)) ;
 
 behavior matrix_valid :
    assumes A != \null ;
    assumes matrix_valid(A) ;
 
    requires A->p_shallow == 0 ;
    requires freeable_storage(A) ;
 
    ensures \result == GrB_SUCCESS ==>
                matrix_storage_init(A) &&
                matrix_valid(A)        &&
                freeable_storage(A) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
GrB_Info GrB_Matrix_clear   // clear a matrix of all entries;
(                           // type and dimensions remain unchanged
    GrB_Matrix A            // matrix to clear
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    WHERE ("GrB_Matrix_clear (A)") ;
    RETURN_IF_NULL_OR_UNINITIALIZED (A) ;

    //--------------------------------------------------------------------------
    // clear the matrix
    //--------------------------------------------------------------------------

    GB_Matrix_clear (A) ;
    return (REPORT_SUCCESS) ;
}

