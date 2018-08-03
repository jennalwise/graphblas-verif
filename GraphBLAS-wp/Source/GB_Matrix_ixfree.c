//------------------------------------------------------------------------------
// GB_Matrix_ixfree: free A->i, A->x, pending tuples, zombies; A->p unchanged
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 7/28/18 ***
// GB_Matrix_ixfree

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 behavior matrix_null :
    assumes A == \null ;
    frees \nothing ;
    assigns \nothing ;
    ensures A == \null ;
 
 behavior matrix_invalid :
    assumes A != \null ;
    assumes \valid(A) ;
    assumes !matrix_valid(A) ;
 
    requires A->npending >= 0 ;
    requires A->nzombies >= 0 ;
    requires type_valid(matrix_type(A)) ;
    requires matrix_fp_separated(A) ;
    requires (!(A->i_shallow) && A->i != \null ==> \freeable(A->i)) ;
    requires (!(A->x_shallow) && A->x != \null ==> \freeable(A->x)) ;
    requires (A->ipending != \null ==> \freeable(A->ipending)) ;
    requires (A->jpending != \null ==> \freeable(A->jpending)) ;
    requires (A->xpending != \null ==> \freeable(A->xpending)) ;
 
    frees A->i ;
    frees A->x ;
    frees A->ipending ;
    frees A->jpending ;
    frees A->xpending ;
 
    assigns __fc_heap_status ;
 
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
 
    ensures A->i == \null ;
    ensures A->x == \null ;
    ensures A->i_shallow == \false ;
    ensures A->x_shallow == \false ;
    ensures matrix_nvals(A) == 0 ;
    ensures A->nzombies == 0 ;
 
    ensures A->ipending == \null ;
    ensures A->jpending == \null ;
    ensures A->xpending == \null ;
    ensures A->npending == 0 ;
    ensures A->max_npending == 0 ;
    ensures A->sorted_pending == \true ;
    ensures A->operator_pending == \null ;
 
    ensures A->queue_prev == \null ;
    ensures A->queue_next == \null ;
    ensures A->enqueued == \false ;
 
 behavior matrix_valid :
    assumes A != \null ;
    assumes matrix_valid(A) ;
 
    requires A->npending >= 0 ;
    requires A->nzombies >= 0 ;
    requires (!(A->i_shallow) && A->i != \null ==> \freeable(A->i)) ;
    requires (!(A->x_shallow) && A->x != \null ==> \freeable(A->x)) ;
    requires (A->ipending != \null ==> \freeable(A->ipending)) ;
    requires (A->jpending != \null ==> \freeable(A->jpending)) ;
    requires (A->xpending != \null ==> \freeable(A->xpending)) ;
 
    frees A->i ;
    frees A->x ;
    frees A->ipending ;
    frees A->jpending ;
    frees A->xpending ;
 
    assigns __fc_heap_status ;
 
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
 
    ensures matrix_valid(A) ;
 
    ensures A->i == \null ;
    ensures A->x == \null ;
    ensures A->i_shallow == \false ;
    ensures A->x_shallow == \false ;
    ensures matrix_nvals(A) == 0 ;
    ensures A->nzombies == 0 ;
 
    ensures A->ipending == \null ;
    ensures A->jpending == \null ;
    ensures A->xpending == \null ;
    ensures A->npending == 0 ;
    ensures A->max_npending == 0 ;
    ensures A->sorted_pending == \true ;
    ensures A->operator_pending == \null ;
 
    ensures A->queue_prev == \null ;
    ensures A->queue_next == \null ;
    ensures A->enqueued == \false ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
void GB_Matrix_ixfree       // free all but A->p
(
    GrB_Matrix A
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    if (A == NULL)
    {
        return ;
    }

    //--------------------------------------------------------------------------
    // free all but A->p
    //--------------------------------------------------------------------------

    // zombies and pending tuples are about to be deleted
    ASSERT (PENDING_OK (A)) ;
    ASSERT (ZOMBIES_OK (A)) ;

    // free A->i unless it is shallow
    if (!A->i_shallow)
    {
        GB_FREE_MEMORY (A->i, A->nzmax, sizeof (int64_t)) ;
    }
    A->i = NULL ;
    A->i_shallow = false ;

    // free A->x unless it is shallow
    if (!A->x_shallow)
    {
        GB_FREE_MEMORY (A->x, A->nzmax, A->type->size) ;
    }
    A->x = NULL ;
    A->x_shallow = false ;

    A->nzmax = 0 ;

    // no zombies remain
    A->nzombies = 0 ;

    // free pending tuples
    GB_free_pending (A) ;

    // remove from the queue, if present
    GB_queue_remove (A) ;
}

