// SuiteSparse:GraphBLAS:Verification, Jenna L. Wise, (c) 2018, All Rights Reserved.
//  Last updated on 7/27/18

#include "GraphBLAS.h"
#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

int main(void) {
    
    GrB_Matrix A = NULL ;
    GrB_Index A_nrows ;
    GrB_Index A_ncols ;
    GrB_Info info ;
    
    info = GrB_Matrix_new(&A, GrB_INT32, 10, 2) ;
    if (info != GrB_SUCCESS) {
        //@ assert A == \null ;
        GrB_Matrix_free(&A) ;
        //@ assert A == \null ;
        //@ assert type_valid(GrB_INT32) ;
        return 0 ;
    }
    //@ assert matrix_valid(A) ;
    //@ assert matrix_type(A) == GrB_INT32 ;
    
    GrB_Matrix_nrows(&A_nrows, A) ;
    if (info != GrB_SUCCESS) {
        GrB_Matrix_free(&A) ;
        //@ assert A == \null ;
        //@ assert type_valid(GrB_INT32) ;
        return 0 ;
    }
    
    //@ assert matrix_valid(A) && A_nrows == matrix_nrows(A) == 10 ;
    
    GrB_Matrix_ncols(&A_ncols, A) ;
    if (info != GrB_SUCCESS) {
        GrB_Matrix_free(&A) ;
        //@ assert A == \null ;
        //@ assert type_valid(GrB_INT32) ;
        return 0 ;
    }
    
    //@ assert matrix_valid(A) && A_ncols == matrix_ncols(A) == 2 ;
    
    A->x = GB_calloc_memory(2,sizeof(int32_t)) ;
    if (A->x == NULL) {
        GrB_Matrix_free(&A) ;
        //@ assert A == \null ;
        //@ assert type_valid(GrB_INT32) ;
        return 0 ;
    }
    A->i = GB_calloc_memory(2,sizeof(int64_t)) ;
    if (A->i == NULL) {
        GB_FREE_MEMORY (A->x,2,sizeof(int32_t)) ;
        GrB_Matrix_free(&A) ;
        //@ assert A == \null ;
        //@ assert type_valid(GrB_INT32) ;
        return 0 ;
    }
    
    A->nzmax = 2 ;
    //@ assert matrix_valid(A) ;
    
    (A->p)[1] = 1 ;
    (A->p)[2] = 2 ;
    (A->i)[(A->p)[0]] = 2 ;
    (A->i)[(A->p)[1]] = 3 ;
    ((int32_t*)(A->x))[(A->p)[0]] = 5 ;
    ((int32_t*)(A->x))[(A->p)[1]] = 4 ;
    
    //@ assert matrix_valid(A) ;
    
    GrB_Matrix_clear(A) ;
    //@ assert \forall int64_t k; 0 <= k <= matrix_ncols(A) ==> (A->p)[k] == 0 ;
    //@ assert A->i == \null && A->x == \null ;
    //@ assert matrix_valid(A) ;
    
    GrB_Matrix_free(&A) ;
    //@ assert A == \null ;
    //@ assert type_valid(GrB_INT32) ;
    
    /*
    int *arr1 = GB_calloc_memory(10,sizeof(int)) ;
    if (arr1 == NULL) { return 0 ; }
    arr1[2] = 6 ;
    int *arr2 = GB_calloc_memory(10,sizeof(int)) ;
    if (arr2 == NULL) { return 0 ; }
    arr2[2] = 3 ;
    GB_cast_array(arr1, GB_INT32_code, arr2, GB_INT32_code, 10) ;
    // assert arr1[2] == 3 && arr2[2] == 3 ;
    */
    return 0 ;
}
