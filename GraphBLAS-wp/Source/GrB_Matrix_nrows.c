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
 requires \separated(&GB_thread_local,\union(nrows,A)) ;
 requires \separated(GB_thread_local.where,\union(nrows,A)) ;
 requires \separated(GB_thread_local.file,\union(nrows,A)) ;
 behavior input_invalid:
    assumes nrows == \null  ||
            A == \null      ||
            !matrix_valid(A) ;
    assigns GB_thread_local.where ;
    assigns GB_thread_local.file ;
    assigns GB_thread_local.line ;
    assigns GB_thread_local.info ;
    ensures (\result == GrB_NULL_POINTER ==>
                nrows == \null || A == \null)        ||
            (\result == GrB_INVALID_OBJECT ==>
                !matrix_valid(A))                    ||
            (\result == GrB_UNINITIALIZED_OBJECT ==>
                nrows != \null &&
                \valid(A)      &&
                !matrix_init(A))                     ||
            \result == GrB_PANIC ;
 behavior input_valid_no_alias:
    assumes nrows != \null ;
    assumes A != \null ;
    assumes matrix_valid(A) ;
    assumes \separated(nrows,A) ;
    requires \valid(nrows) ;
    assigns *nrows ;
    assigns GB_thread_local.where ;
    assigns GB_thread_local.info ;
    ensures (\result == GrB_SUCCESS ==>
                matrix_valid(A)           &&
                *nrows == matrix_nrows(A) &&
                \valid(nrows))            ||
            \result == GrB_PANIC ;
 behavior input_valid_alias:
    assumes nrows != \null ;
    assumes A != \null ;
    assumes matrix_valid(A) ;
    assumes !\separated(nrows,A) ;
    requires \valid(nrows) ;
    assigns *nrows ;
    assigns GB_thread_local.where ;
    assigns GB_thread_local.info ;
    ensures  (\result == GrB_SUCCESS ==> \valid(nrows)) ||
             \result == GrB_PANIC ;
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

