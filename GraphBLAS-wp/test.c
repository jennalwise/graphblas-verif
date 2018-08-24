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
    
    info = GrB_Matrix_new(&A, GrB_INT32, 10, 4) ;
    if (info != GrB_SUCCESS) {
        //@ assert A == \null ;
        GrB_Matrix_free(&A) ; return 0 ;
    }
    //@ assert matrix_valid(A) ;
    
    GrB_Matrix_nrows(&A_nrows, A) ;
    if (info != GrB_SUCCESS) { GrB_Matrix_free(&A) ; return 0 ; }
    
    GrB_Matrix_ncols(&A_ncols, A) ;
    if (info != GrB_SUCCESS) { GrB_Matrix_free(&A) ; return 0 ; }
    
    //GB_AxB_numeric(C, NULL, A, B, GxB_PLUS_TIMES_INT32, false, false) ;
    
    GrB_Matrix_free(&A) ;
    //@ assert type_valid(GrB_INT32) ;
    return 0 ;
}
