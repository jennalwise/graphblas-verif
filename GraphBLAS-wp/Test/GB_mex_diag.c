//------------------------------------------------------------------------------
// GB_mex_diag: compute C=diag(A,1)
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

//------------------------------------------------------------------------------

// C = diag (A,k), where A and C are double

#include "GB_mex.h"

#define FREE_ALL                        \
{                                       \
    GB_MATRIX_FREE (&A) ;               \
    GB_MATRIX_FREE (&C) ;               \
    GB_mx_put_global (malloc_debug) ;   \
}


void mexFunction
(
    int nargout,
    mxArray *pargout [ ],
    int nargin,
    const mxArray *pargin [ ]
)
{

    bool malloc_debug = GB_mx_get_global ( ) ;
    GrB_Matrix A = NULL, C = NULL ;

    // check inputs
    if (nargout > 1 || nargin < 1 || nargin > 2)
    {
        mexErrMsgTxt ("Usage: C = GB_mex_diag (A,k)") ;
    }

    #define GET_DEEP_COPY ;
    #define FREE_DEEP_COPY ;

    // get A
    A = GB_mx_mxArray_to_Matrix (pargin [0], "A", false) ;
    if (A == NULL)
    {
        FREE_ALL ;
        mexErrMsgTxt ("failed") ;
    }

    int64_t k = 0 ;
    // get k
    if (nargin > 1)
    {
        k = (int64_t) mxGetScalar (pargin [1]) ;
    }

    // construct C
    METHOD (GrB_Matrix_new (&C, GrB_FP64, A->nrows, A->ncols)) ;

    // C = diag (A,k)
    METHOD (GxB_Matrix_select (C, NULL, NULL, GxB_DIAG, A, &k, NULL)) ;

    // return C to MATLAB as a regular MATLAB sparse matrix
    pargout [0] = GB_mx_Matrix_to_mxArray (&C, "C diag", false) ;

    FREE_ALL ;
}

