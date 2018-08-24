//------------------------------------------------------------------------------
// GB_Matrix_free: free a matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA Changed 8/23/18 ***
// Moved GB_Matrix_ixfree (A) ; to above freeing p and setting magic to freed,
// because want to adhere to specification should probably change specification
// rather than change this, but it would be a rather large change

// *** JENNA ANNOTATION 7/29/18 ***
// GB_Matrix_free

//------------------------------------------------------------------------------

// free all the content of a matrix.  After GB_Matrix_free (&A), A is set
// to NULL.  This function is not user-callable; use GrB_Matrix_free instead.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires (matrix != \null ==> \valid(matrix)) ;
 requires (\valid(matrix) && *matrix != \null ==> \valid(*matrix)) ;
 requires (\valid(matrix) && \valid(*matrix) &&
           (matrix_init(*matrix) || matrix_malloc_init(*matrix)) ==>
                type_valid(matrix_type(*matrix)) &&
                0 <= matrix_ncols(*matrix)+1 <= INT64_MAX) ;
 
 frees *matrix ;
 frees (*matrix)->p ;
 frees (*matrix)->i ;
 frees (*matrix)->x ;
 frees (*matrix)->ipending ;
 frees (*matrix)->jpending ;
 frees (*matrix)->xpending ;
 
 assigns __fc_heap_status ;
 
 assigns *matrix ;
 assigns (*matrix)->magic ;
 assigns (*matrix)->p ;
 assigns (*matrix)->i ;
 assigns (*matrix)->i_shallow ;
 assigns (*matrix)->x ;
 assigns (*matrix)->x_shallow ;
 assigns (*matrix)->nzmax ;
 assigns (*matrix)->nzombies ;
 assigns (*matrix)->ipending ;
 assigns (*matrix)->jpending ;
 assigns (*matrix)->xpending ;
 assigns (*matrix)->npending ;
 assigns (*matrix)->max_npending ;
 assigns (*matrix)->sorted_pending ;
 assigns (*matrix)->operator_pending ;
 assigns (*matrix)->queue_prev ;
 assigns (*matrix)->queue_next ;
 assigns (*matrix)->enqueued ;
 
 behavior matrix_ptr_null :
    assumes matrix == \null ;
    ensures matrix == \null ;
 
 behavior matrix_null :
    assumes \valid(matrix) ;
    assumes *matrix == \null ;
    ensures *matrix == \null ;
 
 behavior matrix_not_init :
    assumes \valid(matrix) ;
    assumes \valid(*matrix) ;
    assumes !matrix_init(*matrix) ;
    assumes !matrix_malloc_init(*matrix) ;
    ensures *matrix == \null ;
 
 behavior matrix_valid :
    assumes \valid(matrix) ;
    assumes \valid(*matrix) ;
    assumes (matrix_init(*matrix) ||
             matrix_malloc_init(*matrix)) ;
 
    requires (matrix_valid(*matrix) ||
              matrix_malloc_valid(*matrix)) ;
    requires 0 <= matrix_ncols(*matrix)+1 <= INT64_MAX ;
    requires \freeable(*matrix) ;
    requires freeable_storage(*matrix) ;
 
    ensures *matrix == \null ;
 
 disjoint behaviors ;
 */
void GB_Matrix_free             // free a matrix
(
    GrB_Matrix *matrix          // handle of matrix to free
)
{

    if (matrix != NULL)
    {
        GrB_Matrix A = *matrix ;
        if (A != NULL && (A->magic == MAGIC || A->magic == MAGIC2))
        {
            GB_Matrix_ixfree (A) ;
            A->magic = FREED ;      // to help detect dangling pointers
            if (!A->p_shallow)
            {
                GB_FREE_MEMORY (A->p, A->ncols+1, sizeof (int64_t)) ;
            }
            A->p = NULL ;
            
            GB_FREE_MEMORY (*matrix, 1, sizeof (struct GB_Matrix_opaque)) ;
        }
        (*matrix) = NULL ;
    }
}

