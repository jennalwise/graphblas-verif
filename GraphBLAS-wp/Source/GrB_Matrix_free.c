//------------------------------------------------------------------------------
// GrB_Matrix_free: free a matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/10/18 ***
// GrB_Matrix_free

//------------------------------------------------------------------------------

// free all the content of a matrix.  After GrB_Matrix_free (&A), A is set
// to NULL

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 frees *A ;
 frees (*A)->p ;
 frees (*A)->i ;
 frees (*A)->x ;
 frees (*A)->ipending ;
 frees (*A)->jpending ;
 frees (*A)->xpending ;
 
 assigns __fc_heap_status ;
 
 assigns *A ;
 assigns (*A)->magic ;
 assigns (*A)->p ;
 assigns (*A)->i ;
 assigns (*A)->i_shallow ;
 assigns (*A)->x ;
 assigns (*A)->x_shallow ;
 assigns (*A)->nzmax ;
 assigns (*A)->nzombies ;
 assigns (*A)->ipending ;
 assigns (*A)->jpending ;
 assigns (*A)->xpending ;
 assigns (*A)->npending ;
 assigns (*A)->max_npending ;
 assigns (*A)->sorted_pending ;
 assigns (*A)->operator_pending ;
 assigns (*A)->queue_prev ;
 assigns (*A)->queue_next ;
 assigns (*A)->enqueued ;
 
 ensures (\result == GrB_SUCCESS ||
          \result == GrB_PANIC) ;
 
 behavior matrix_ptr_null :
    assumes A == \null ;
    ensures \result == GrB_SUCCESS ==> A == \null ;
 
 behavior matrix_null :
    assumes \valid(A) ;
    assumes *A == \null ;
    ensures \result == GrB_SUCCESS ==> *A == \null ;
 
 behavior matrix_not_init :
    assumes \valid(A) ;
    assumes \valid(*A) ;
    assumes !matrix_init(*A) ;
    assumes !matrix_malloc_init(*A) ;
    ensures \result == GrB_SUCCESS ==> *A == \null ;
 
 behavior matrix_valid :
    assumes \valid(A) ;
    assumes \valid(*A) ;
    assumes (matrix_init(*A) ||
             matrix_malloc_init(*A)) ;
 
    requires (matrix_valid(*A) ||
              matrix_malloc_valid(*A)) ;
    requires 0 <= matrix_ncols(*A)+1 <= INT64_MAX ;
    requires \freeable(*A) ;
    requires freeable_storage(*A) ;
 
    ensures \result == GrB_SUCCESS ==>
                *A == \null ;
 
 disjoint behaviors ;
 */
GrB_Info GrB_Matrix_free        // free a matrix
(
    GrB_Matrix *A               // handle of matrix to free
)
{

    GB_MATRIX_FREE (A) ;
    return (GrB_SUCCESS) ;
}

