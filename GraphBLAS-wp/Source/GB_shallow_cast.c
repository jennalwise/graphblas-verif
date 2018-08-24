//------------------------------------------------------------------------------
// GB_shallow_cast: create a shallow copy of a matrix, optionally typecasted
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/4/18 ***
// GB_shallow_cast

//------------------------------------------------------------------------------

// C = (ctype) A.

// Create a shallow copy of a matrix, possibly typecasted.

// The values are a shallow copy unless they need to be typecasted.

// The pattern is always a shallow copy.  No errors are checked except for
// out-of-memory conditions.  This function is not user-callable.  Shallow
// matrices are never passed back to the user.

// Compare this function with GB_shallow_op.c

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires \valid(shallow_cast_handle) ;
 requires *shallow_cast_handle == \null ;
 requires matrix_valid(A) ;
 requires type_valid(ctype) ;
 requires type_compatible{Here,Here}(ctype, matrix_type(A)) ;
 requires (matrix_nvals(A) == 0) == (A->i == \null && A->x == \null) ;
 requires !(A->npending > 0) ;
 requires !(A->nzombies > 0) ;
 
 requires \separated(shallow_cast_handle,\union(ctype,A)) ;
 requires \separated(ctype,A) ; // no matrix_fp with A->type
 requires \separated(&GB_thread_local,\union(shallow_cast_handle,ctype,A)) ;
 requires \separated(GB_thread_local.file,\union(shallow_cast_handle,ctype,A)) ;
 
 allocates *shallow_cast_handle ;
 
 assigns __fc_heap_status ;
 
 assigns GB_thread_local.file ;
 assigns GB_thread_local.line ;
 assigns GB_thread_local.info ;
 
 assigns *shallow_cast_handle ;
 assigns \at((*shallow_cast_handle),Post)->magic ;
 assigns \at((*shallow_cast_handle),Post)->type ;
 assigns \at((*shallow_cast_handle),Post)->nrows ;
 assigns \at((*shallow_cast_handle),Post)->ncols ;
 assigns \at((*shallow_cast_handle),Post)->nzmax ;
 assigns \at((*shallow_cast_handle),Post)->p ;
 assigns \at((*shallow_cast_handle),Post)->i ;
 assigns *((((char*)(\at((*shallow_cast_handle),Post)->x)) +
            (0..\at((*shallow_cast_handle),Post)->type->size-1)) +
                (0..nnz(A)-1)) ;
 assigns \at((*shallow_cast_handle),Post)->p_shallow ;
 assigns \at((*shallow_cast_handle),Post)->i_shallow ;
 assigns \at((*shallow_cast_handle),Post)->x_shallow ;
 assigns \at((*shallow_cast_handle),Post)->npending ;
 assigns \at((*shallow_cast_handle),Post)->max_npending ;
 assigns \at((*shallow_cast_handle),Post)->sorted_pending ;
 assigns \at((*shallow_cast_handle),Post)->operator_pending ;
 assigns \at((*shallow_cast_handle),Post)->ipending ;
 assigns \at((*shallow_cast_handle),Post)->jpending ;
 assigns \at((*shallow_cast_handle),Post)->xpending ;
 assigns \at((*shallow_cast_handle),Post)->queue_next ;
 assigns \at((*shallow_cast_handle),Post)->queue_prev ;
 assigns \at((*shallow_cast_handle),Post)->enqueued ;
 assigns \at((*shallow_cast_handle),Post)->nzombies ;
 
 ensures (\result == GrB_OUT_OF_MEMORY ||
          \result == GrB_SUCCESS) ;
 ensures (\result == GrB_OUT_OF_MEMORY ==>
            *shallow_cast_handle == \null &&
            matrix_valid(A)) ;
 ensures (\result == GrB_SUCCESS ==>
            (*shallow_cast_handle)->p == A->p                     &&
            (*shallow_cast_handle)->p_shallow == 1                &&
            matrix_init(*shallow_cast_handle)                     &&
            matrix_type(*shallow_cast_handle) == ctype            &&
            matrix_nrows(*shallow_cast_handle) == matrix_nrows(A) &&
            matrix_ncols(*shallow_cast_handle) == matrix_ncols(A) &&
            (*shallow_cast_handle)->npending == 0                 &&
            (*shallow_cast_handle)->max_npending == 0             &&
            (*shallow_cast_handle)->sorted_pending == 1           &&
            (*shallow_cast_handle)->operator_pending == \null     &&
            (*shallow_cast_handle)->ipending == \null             &&
            (*shallow_cast_handle)->jpending == \null             &&
            (*shallow_cast_handle)->xpending == \null             &&
            (*shallow_cast_handle)->queue_next == \null           &&
            (*shallow_cast_handle)->queue_prev == \null           &&
            (*shallow_cast_handle)->enqueued == 0                 &&
            (*shallow_cast_handle)->nzombies == 0                 &&
            matrix_valid(*shallow_cast_handle)                    &&
            \freeable(*shallow_cast_handle)                       &&
            freeable_storage(*shallow_cast_handle)                &&
            matrix_valid(A)) ;
 
 behavior A_nzmax_zero :
    assumes matrix_nvals(A) == 0 ;
    ensures (\result == GrB_SUCCESS ==>
                matrix_nvals(*shallow_cast_handle) == 0     &&
                (*shallow_cast_handle)->i == \null          &&
                (*shallow_cast_handle)->x == \null          &&
                (*shallow_cast_handle)->i_shallow == 0      &&
                (*shallow_cast_handle)->x_shallow == 0) ;
 
 behavior matrix_types_same :
    assumes matrix_nvals(A) >= max(nnz(A),1) ;
    assumes ctype == matrix_type(A) ;
    ensures (\result == GrB_SUCCESS ==>
                matrix_nvals(*shallow_cast_handle) == matrix_nvals(A) &&
                (*shallow_cast_handle)->i == A->i                     &&
                (*shallow_cast_handle)->x == A->x                     &&
                (*shallow_cast_handle)->i_shallow == 1                &&
                (*shallow_cast_handle)->x_shallow == 1) ;
 
 behavior matrix_types_not_same :
    assumes matrix_nvals(A) >= max(nnz(A),1) ;
    assumes ctype != matrix_type(A) ;
    ensures (\result == GrB_SUCCESS ==>
                matrix_nvals(*shallow_cast_handle) == (int64_t)max(nnz(A),1)   &&
                (*shallow_cast_handle)->i == A->i                               &&
                array_unchanged{Pre,Here}(A->x,
                                          type_code(matrix_type(A)),
                                          nnz(A))                               &&
                array_cast{Here,Pre}((*shallow_cast_handle)->x,
                                     A->x,
                                     type_code(matrix_type(*shallow_cast_handle)),
                                     type_code(matrix_type(A)),
                                     nnz(A))                                    &&
                (*shallow_cast_handle)->i_shallow == 1                          &&
                (*shallow_cast_handle)->x_shallow == 0) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
GrB_Info GB_shallow_cast                // create a shallow typecasted matrix
(
    GrB_Matrix *shallow_cast_handle,    // output matrix to typecast into
    const GrB_Type ctype,               // type of the output matrix C
    const GrB_Matrix A                  // input matrix to typecast
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    ASSERT (shallow_cast_handle != NULL && *shallow_cast_handle == NULL) ;
    ASSERT_OK (GB_check (A, "A for shallow cast", 0)) ;
    ASSERT_OK (GB_check (ctype, "ctype for typecast", 0)) ;
    ASSERT (GB_Type_compatible (ctype, A->type)) ;
    ASSERT ((A->nzmax == 0) == (A->i == NULL && A->x == NULL)) ;
    ASSERT (!PENDING (A)) ; ASSERT (!ZOMBIES (A)) ;

    //--------------------------------------------------------------------------
    // construct a shallow copy of A for the pattern of C
    //--------------------------------------------------------------------------

    // allocate the struct for C, but do not allocate C->p, C->i, or C->x
    GrB_Info info ;
    GB_NEW (shallow_cast_handle, ctype, A->nrows, A->ncols, false, false) ;
    if (info != GrB_SUCCESS)
    {
        return (info) ;
    }
    
    GrB_Matrix C = *shallow_cast_handle ;

    //--------------------------------------------------------------------------
    // make a shallow copy of the column pointers
    //--------------------------------------------------------------------------

    ASSERT (C->magic == MAGIC2) ;   // [ be careful; C is not yet initialized
    C->p = A->p ;                   // C->p is of size A->ncols + 1
    C->p_shallow = true ;           // C->p will not be freed when freeing C
    C->magic = MAGIC ;              // C is now initialized ]

    //--------------------------------------------------------------------------
    // check for empty matrix
    //--------------------------------------------------------------------------

    if (A->nzmax == 0)
    {
        // C->p is shallow but the rest is empty
        C->nzmax = 0 ;
        C->i = NULL ;
        C->x = NULL ;
        C->i_shallow = false ;
        C->x_shallow = false ;
        ASSERT_OK (GB_check (C, "C = quick copy of empty (A)", 0)) ;
        return (REPORT_SUCCESS) ;
    }

    //--------------------------------------------------------------------------
    // make a shallow copy of the pattern
    //--------------------------------------------------------------------------

    C->i = A->i ;               // of size A->nzmax
    C->i_shallow = true ;       // C->i will not be freed when freeing C

    //--------------------------------------------------------------------------
    // make a shallow copy of the values, or allocate new ones
    //--------------------------------------------------------------------------

    int64_t anz = NNZ (A) ;
    ASSERT (A->nzmax >= IMAX (anz,1)) ;

    if (C->type == A->type)
    {
        // no work is done at all.  C is a pure shallow copy
        C->nzmax = A->nzmax ;
        C->x = A->x ;
        C->x_shallow = true ;       // C->x will not be freed when freeing C
        ASSERT_OK (GB_check (C, "C = pure shallow (A)", 0)) ;
        return (REPORT_SUCCESS) ;
    }

    // allocate new space for the numerical values of C
    C->nzmax = IMAX (anz,1) ;
    GB_MALLOC_MEMORY (C->x, C->nzmax, C->type->size) ;
    C->x_shallow = false ;          // free C->x when freeing C
    double memory = GBYTES (C->nzmax, C->type->size) ;
    if (C->x == NULL)
    {
        // out of memory
        GB_MATRIX_FREE (shallow_cast_handle) ;
        return (ERROR (GrB_OUT_OF_MEMORY, (LOG,
            "out of memory, %g GBytes required", memory))) ;
    }

    //--------------------------------------------------------------------------
    // copy the values from A into C and cast from A->type to C->type
    //--------------------------------------------------------------------------

    GB_cast_array (C->x, C->type->code, A->x, A->type->code, anz) ;

    // C->i always shallow, and is of size at least A->nzmax.  The array C->x
    // is either of size A->nzmax if C->x is and not typecasted, or
    // IMAX(anz,1) otherwise.  Thus, the two arrays C->i and C->x can differ
    // in size if C->x is typecasted.  C->nzmax reflects this, and has been set
    // to the smaller of the two sizes.

    ASSERT_OK (GB_check (C, "C = shallow (A)", 0)) ;
    return (REPORT_SUCCESS) ;
}

