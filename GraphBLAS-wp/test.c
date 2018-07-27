// SuiteSparse:GraphBLAS:Verification, Jenna L. Wise, (c) 2018, All Rights Reserved.
//  Last updated on 7/27/18

#include "GraphBLAS.h"
#include "GB.h"

int main(void) {
    
    GrB_Matrix C = NULL ;
    GrB_Matrix A = NULL ;
    GrB_Matrix B = NULL ;
    GrB_Index A_nrows ;
    GrB_Index A_ncols ;
    
    GrB_Matrix_new(&C, GrB_INT32, 10, 10) ;
    GrB_Matrix_new(&A, GrB_INT32, 10, 4) ;
    GrB_Matrix_new(&B, GrB_INT32, 4, 10) ;
    
    GrB_Matrix_nrows(&A_nrows, A) ;
    GrB_Matrix_ncols(&A_ncols, A) ;
    
    GB_AxB_numeric(C, NULL, A, B, GxB_PLUS_TIMES_INT32, false, false) ;
    
    GrB_Matrix_free(&C) ;
    GrB_Matrix_free(&A) ;
    GrB_Matrix_free(&B) ;
    
    return 0 ;
}
