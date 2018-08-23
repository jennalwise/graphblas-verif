//------------------------------------------------------------------------------
// GrB_Matrix_new: create a new matrix
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/3/18 ***
// GrB_Matrix_new

//------------------------------------------------------------------------------

// The new matrix is nrows-by-ncols, with no entries in it.
// A->p is size ncols+1 and all zero.  Contents A->x and A->i are NULL.
// If this method fails, *A is set to NULL.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires A != \null ==> \valid(A) ;
 requires type != \null ==> type_valid(type) ;
 
 requires \separated(&GB_thread_local,\union(A,type)) ;
 requires (GB_thread_local.where != \null || A != \null) ==>
            \separated(GB_thread_local.where,A) ;
 requires (GB_thread_local.file != \null || A != \null) ==>
            \separated(GB_thread_local.file,A) ;
 requires (A != \null || type != \null) ==>
            \separated(A,type) ;
 
 allocates *A ;
 allocates \at((*A),Post)->p ;
 
 //assigns __fc_heap_status ;
 
 //assigns GB_thread_local.where ;
 //assigns GB_thread_local.file ;
 //assigns GB_thread_local.line ;
 //assigns GB_thread_local.info ;
 
 //assigns *A ;
 //assigns \at((*A),Post)->magic ;
 //assigns \at((*A),Post)->type ;
 //assigns \at((*A),Post)->nrows ;
 //assigns \at((*A),Post)->ncols ;
 //assigns \at((*A),Post)->nzmax ;
 //assigns \at((*A),Post)->p ;
 //assigns \at((*A),Post)->i ;
 //assigns \at((*A),Post)->x ;
 //assigns \at((*A),Post)->p_shallow ;
 //assigns \at((*A),Post)->i_shallow ;
 //assigns \at((*A),Post)->x_shallow ;
 //assigns \at((*A),Post)->npending ;
 //assigns \at((*A),Post)->max_npending ;
 //assigns \at((*A),Post)->sorted_pending ;
 //assigns \at((*A),Post)->operator_pending ;
 //assigns \at((*A),Post)->ipending ;
 //assigns \at((*A),Post)->jpending ;
 //assigns \at((*A),Post)->xpending ;
 //assigns \at((*A),Post)->queue_next ;
 //assigns \at((*A),Post)->queue_prev ;
 //assigns \at((*A),Post)->enqueued ;
 //assigns \at((*A),Post)->nzombies ;
 
 behavior matrix_handle_null :
    assumes A == \null ;
    ensures (\result == GrB_NULL_POINTER ||
             \result == GrB_PANIC) ;
    ensures (\result == GrB_NULL_POINTER ==>
                A == \null) ;
 
 behavior inputs_invalid :
    assumes A != \null ;
    assumes (nrows > ((GrB_Index)(1ULL << 60)) ||
             ncols > ((GrB_Index)(1ULL << 60)) ||
             !type_valid(type)) ;
    requires \valid(A) ;
    ensures (\result == GrB_NULL_POINTER         ||
             \result == GrB_UNINITIALIZED_OBJECT ||
             \result == GrB_INVALID_OBJECT       ||
             \result == GrB_INVALID_VALUE        ||
             \result == GrB_PANIC) ;
    ensures (\result == GrB_NULL_POINTER ==>
                *A == \null &&
                type == \null
            ) ;
    ensures (\result == GrB_UNINITIALIZED_OBJECT ==>
                *A == \null &&
                !type_init(type)
            ) ;
    ensures (\result == GrB_INVALID_OBJECT ==>
                *A == \null &&
                !type_valid(type)
            ) ;
    ensures (\result == GrB_INVALID_VALUE ==>
                *A == \null &&
                (nrows > ((GrB_Index)(1ULL << 60)) ||
                 ncols > ((GrB_Index)(1ULL << 60)))
            ) ;
 
 behavior inputs_valid :
    assumes A != \null ;
    assumes type_valid(type) ;
    assumes nrows <= ((GrB_Index)(1ULL << 60)) ;
    assumes ncols <= ((GrB_Index)(1ULL << 60)) ;
    requires \valid(A) ;
    ensures (\result == GrB_SUCCESS ||
             \result == GrB_OUT_OF_MEMORY) ;
    ensures (\result == GrB_OUT_OF_MEMORY ==> *A == \null) ;
    ensures (\result == GrB_SUCCESS ==>
                matrix_type(*A) == type            &&
                matrix_nrows(*A) == (int64_t)nrows &&
                matrix_ncols(*A) == (int64_t)ncols &&
                matrix_nvals(*A) == 0              &&
                matrix_storage_init(*A)            &&
                !matrix_malloc_init(*A)            &&
                !matrix_malloc_valid(*A)           &&
                matrix_init(*A)                    &&
                matrix_valid(*A)                   &&
                \at(*A,Pre) != *A                  &&
                \freeable(*A)                      &&
                freeable_storage(*A)) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
GrB_Info GrB_Matrix_new     // create a new matrix with no entries
(
    GrB_Matrix *A,          // handle of matrix to create
    const GrB_Type type,    // type of matrix to create
    const GrB_Index nrows,  // matrix dimension is nrows-by-ncols
    const GrB_Index ncols
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    WHERE ("GrB_Matrix_new (&A, type, nrows, ncols)") ;
    RETURN_IF_NULL (A) ;
    (*A) = NULL ;
    RETURN_IF_NULL_OR_UNINITIALIZED (type) ;

    if (nrows > GB_INDEX_MAX)
    {
        // problem too large
        return (ERROR (GrB_INVALID_VALUE, (LOG,
            "problem too large: nrows "GBu" > "GBu, nrows, GB_INDEX_MAX))) ;
    }

    if (ncols > GB_INDEX_MAX)
    {
        // problem too large
        return (ERROR (GrB_INVALID_VALUE, (LOG,
            "problem too large: ncols "GBu" > "GBu, ncols, GB_INDEX_MAX))) ;
    }

    //--------------------------------------------------------------------------
    // create the matrix
    //--------------------------------------------------------------------------

    GrB_Info info ;
    GB_NEW (A, type, nrows, ncols, true, false) ;
    return (info) ;
}

