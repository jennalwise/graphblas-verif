//------------------------------------------------------------------------------
// GB_Matrix_clear: clears the content of a matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/5/18 ***
// GB_Matrix_clear

//------------------------------------------------------------------------------

// The A->x and A->i content is freed and the column pointers A->p are set to
// zero.  This puts the matrix A in the same state it had after GrB_Matrix_new
// (&A, ...).  The dimensions and type of A are not changed.  To change the
// size or type requires a GrB_Matrix_free (&A) followed by another call to
// GrB_Matrix_new (&A, ...) with the new dimensions and type.

// This function is not user-callable.  Use GrB_Matrix_clear instead.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires \valid(A) ;
 requires (matrix_valid(A) || matrix_malloc_valid(A)) ;
 requires A->p_shallow == 0 ;
 requires A->npending >= 0 ;
 requires A->nzombies >= 0 ;
 requires freeable_storage(A) ;
 
 frees A->i ;
 frees A->x ;
 frees A->ipending ;
 frees A->jpending ;
 frees A->xpending ;
 
 assigns __fc_heap_status ;
 
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
 
 ensures matrix_storage_init(A) ;
 ensures matrix_valid(A) ;
 ensures freeable_storage(A) ;
 ensures \forall int64_t k; 0 <= k <= matrix_ncols(A) ==>
            (A->p)[k] == 0 ;
 */
void GB_Matrix_clear        // clear a matrix, type and dimensions unchanged
(
    GrB_Matrix A            // matrix to clear
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    // If A->p is a shallow copy then the p array in the other matrix is
    // cleared too.  GraphBLAS itself does not do this, and it does not return
    // matrices to the user with shallow content.  So assert A->p is not
    // shallow.

    ASSERT (A != NULL && A->p != NULL && !A->p_shallow) ;

    // A has been created by GB_new, which has allocated A->p.  It need not
    // have initialized its contents, however (MAGIC2 case)
    ASSERT (A->magic == MAGIC || A->magic == MAGIC2) ;

    // zombies and pending tuples have no effect; about to delete them anyway
    ASSERT (PENDING_OK (A)) ;
    ASSERT (ZOMBIES_OK (A)) ;

    //--------------------------------------------------------------------------
    // clear the content of A
    //--------------------------------------------------------------------------

    // free all but A->p
    GB_Matrix_ixfree (A) ;

    // no more zombies or pending tuples
    ASSERT (!PENDING (A)) ;
    ASSERT (!ZOMBIES (A)) ;

    // Set the column pointers to zero.
    /*@
     loop invariant 0 <= j <= matrix_ncols(A)+1 ;
     loop invariant
        \forall int64_t k; 0 <= k < j ==>
            (A->p)[k] == 0 ;
     loop assigns j, (A->p)[0..matrix_ncols(A)] ;
     loop variant (matrix_ncols(A)+1) - j ;
     */
    for (int64_t j = 0 ; j <= A->ncols ; j++)
    {
        A->p [j] = 0 ;
    }

    // A is now initialized
    A->magic = MAGIC ;
}

