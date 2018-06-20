//------------------------------------------------------------------------------
// GrB_Matrix_extractElement: extract a single entry from a matrix, x = A(i,j)
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

//------------------------------------------------------------------------------

// Extract the value of single scalar, x = A(i,j), typecasting from the type of
// A to the type of x, as needed.

// Returns GrB_SUCCESS if A(i,j) is present, and sets x to its value.
// Returns GrB_NO_VALUE if A(i,j) is not present, and x is unmodified.

#include "GB.h"

#define EXTRACT(type,T)                                                       \
GrB_Info GrB_Matrix_extractElement_ ## T     /* x = A(i,j) */                 \
(                                                                             \
    type *x,                            /* extracted scalar                */ \
    const GrB_Matrix A,                 /* matrix to extract a scalar from */ \
    const GrB_Index i,                  /* row index                       */ \
    const GrB_Index j                   /* column index                    */ \
)                                                                             \
{                                                                             \
    RETURN_IF_NULL_OR_UNINITIALIZED (A) ;                                     \
    WHERE ("GrB_Matrix_extractElement_" GB_STR(T) " (x, A, i, j)") ;          \
    GrB_Info info = GB_extractElement (x, GB_ ## T ## _code, A, i, j) ;       \
    REPORT_MATRIX (info) ;                                                    \
    return (info) ;                                                           \
}

EXTRACT (bool     , BOOL) ;
EXTRACT (int8_t   , INT8) ;
EXTRACT (uint8_t  , UINT8) ;
EXTRACT (int16_t  , INT16) ;
EXTRACT (uint16_t , UINT16) ;
EXTRACT (int32_t  , INT32) ;
EXTRACT (uint32_t , UINT32) ;
EXTRACT (int64_t  , INT64) ;
EXTRACT (uint64_t , UINT64) ;
EXTRACT (float    , FP32) ;
EXTRACT (double   , FP64) ;
EXTRACT (void     , UDT) ;

#undef EXTRACT

