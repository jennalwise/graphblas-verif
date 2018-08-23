//------------------------------------------------------------------------------
// GrB_Matrix_nrows: number of rows of a sparse matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 7/25/18 ***
// GrB_Matrix_nrows

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires nrows != \null ==> \valid(nrows) ;
 requires A != \null ==> \valid(A) ;
 requires \valid(A) && matrix_init(A) ==> 0 < matrix_nrows(A) <= 1ULL << 60 ;
 
 requires \separated(&GB_thread_local,\union(nrows,A)) ;
 requires (GB_thread_local.where != \null || nrows != \null) ==>
            \separated(GB_thread_local.where,nrows) ;
 requires (GB_thread_local.file != \null || nrows != \null) ==>
            \separated(GB_thread_local.file,nrows) ;
 
 assigns *nrows ;
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
    assumes nrows == \null  ||
            A == \null      ||
            !matrix_valid(A) ;
    ensures (\result == GrB_NULL_POINTER ==>
                nrows == \null || A == \null)        ||
            (\result == GrB_INVALID_OBJECT ==>
                !matrix_valid(A))                    ||
            (\result == GrB_UNINITIALIZED_OBJECT ==>
                nrows != \null &&
                \valid(A)      &&
                !matrix_init(A)) ;
 
 behavior input_valid_no_alias:
    assumes nrows != \null ;
    assumes A != \null ;
    assumes matrix_valid(A) ;
    assumes \separated(nrows,A) ;
    requires \valid(nrows) ;
    ensures \result == GrB_SUCCESS ==>
                matrix_valid(A) &&
                *nrows == matrix_nrows(A) ;
 
 behavior input_valid_alias:
    assumes nrows != \null ;
    assumes A != \null ;
    assumes matrix_valid(A) ;
    assumes !\separated(nrows,A) ;
    requires \valid(nrows) ;
    ensures \result == GrB_SUCCESS ==>
                *nrows == matrix_nrows{Pre}(A) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
GrB_Info GrB_Matrix_nrows   // get the number of rows of a matrix
(
    GrB_Index *nrows,       // matrix has nrows rows
    const GrB_Matrix A      // matrix to query
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    WHERE ("GrB_Matrix_nrows (&nrows, A)") ;
    RETURN_IF_NULL (nrows) ;
    RETURN_IF_NULL_OR_UNINITIALIZED (A) ;

    //--------------------------------------------------------------------------
    // get the number of rows
    //--------------------------------------------------------------------------

    return (GB_Matrix_nrows (nrows, A)) ;
}

