//------------------------------------------------------------------------------
// GrB_Matrix_ncols: number of columns of a sparse matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 7/25/18 ***
// GrB_Matrix_ncols

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires ncols != \null ==> \valid(ncols) ;
 requires A != \null ==> \valid(A) ;
 
 requires \separated(&GB_thread_local,\union(ncols,A)) ;
 requires \separated(GB_thread_local.where,\union(ncols,A)) ;
 requires \separated(GB_thread_local.file,\union(ncols,A)) ;
 
 assigns *ncols ;
 assigns GB_thread_local.where ;
 assigns GB_thread_local.file ;
 assigns GB_thread_local.line ;
 assigns GB_thread_local.info ;
 
 ensures \result == GrB_SUCCESS              ||
         \result == GrB_NULL_POINTER         ||
         \result == GrB_INVALID_OBJECT       ||
         \result == GrB_UNINITIALIZED_OBJECT ||
         \result == GrB_PANIC ;
 
 behavior input_invalid:
    assumes ncols == \null  ||
            A == \null      ||
            !matrix_valid(A) ;
    ensures (\result == GrB_NULL_POINTER ==>
                ncols == \null || A == \null)        ||
            (\result == GrB_INVALID_OBJECT ==>
                !matrix_valid(A))                    ||
            (\result == GrB_UNINITIALIZED_OBJECT ==>
                ncols != \null &&
                \valid(A)      &&
                !matrix_init(A)) ;
 
 behavior input_valid_no_alias:
    assumes ncols != \null ;
    assumes A != \null ;
    assumes matrix_valid(A) ;
    assumes \separated(ncols,A) ;
    requires \valid(ncols) ;
    ensures \result == GrB_SUCCESS ==>
                matrix_valid(A) &&
                *ncols == matrix_ncols(A) ;
 
 behavior input_valid_alias:
    assumes ncols != \null ;
    assumes A != \null ;
    assumes matrix_valid(A) ;
    assumes !\separated(ncols,A) ;
    requires \valid(ncols) ;
    ensures \result == GrB_SUCCESS ==>
                *ncols == matrix_ncols{Pre}(A) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
GrB_Info GrB_Matrix_ncols   // get the number of columns of a matrix
(
    GrB_Index *ncols,       // matrix has ncols columns
    const GrB_Matrix A      // matrix to query
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    WHERE ("GrB_Matrix_ncols (&ncols, A)") ;
    RETURN_IF_NULL (ncols) ;
    RETURN_IF_NULL_OR_UNINITIALIZED (A) ;

    // zombies and pending tuples have no effect on nrows
    // but don't bother asserting that fact here

    //--------------------------------------------------------------------------
    // return the number of columns
    //--------------------------------------------------------------------------

    (*ncols) = A->ncols ;
    return (REPORT_SUCCESS) ;
}

