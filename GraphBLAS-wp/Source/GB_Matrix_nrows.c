//------------------------------------------------------------------------------
// GB_Matrix_nrows: number of rows of a sparse matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 7/25/18 ***
// GB_Matrix_nrows

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires \separated(&GB_thread_local,\union(nrows,A)) ;
 requires nrows != \null ;
 requires A != \null ;
 requires matrix_valid(A) ;
 requires \valid(nrows) ;
 assigns *nrows ;
 assigns GB_thread_local.info ;
 behavior inputs_no_alias:
    assumes \separated(nrows,A) ;
    ensures \result == GrB_SUCCESS ==>
                matrix_valid(A)           &&
                *nrows == matrix_nrows(A) &&
                \valid(nrows) ;
 behavior inputs_alias:
    assumes !\separated(nrows,A) ;
    ensures \result == GrB_SUCCESS ==> \valid(nrows) ;
 */
GrB_Info GB_Matrix_nrows    // get the number of rows of a matrix
(
    GrB_Index *nrows,       // matrix has nrows rows
    const GrB_Matrix A      // matrix to query
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    ASSERT (nrows != NULL) ;
    ASSERT (A != NULL) ;

    // zombies and pending tuples have no effect on nrows
    // but don't bother asserting that fact here

    //--------------------------------------------------------------------------
    // return the number of rows
    //--------------------------------------------------------------------------

    (*nrows) = A->nrows ;
    return (REPORT_SUCCESS) ;
}

