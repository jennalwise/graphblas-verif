//
//  annotlib.acsl
//  
//  SuiteSparse:GraphBLAS:Verification, Jenna L. Wise, (c) 2018, All Rights Reserved.
//  Created on 7/2/18.
//  Last updated on 7/10/18
//  Predicate and logic functions for GrB structs
//  Ensures encapsulation of the structs' internal representation in the annotations

//  IMPORTANT NOTE TO SELF: null ptr checks for input to checks in GB implementation
//                          occur in the check method implementation
//                          I am also doing ptr checks within _valid predicates with
//                          \valid
//                          makes sense since the ptrs are hidden in the typdef

// TODO: Are the {L} labels correct?

#include "GB.h"

//------------------------------------------------------------------------------
// Common
//------------------------------------------------------------------------------

/*@
 logic size_t max{L}(size_t a, size_t b) = a > b ? a : b ;
 
 predicate magic_valid(int64_t magic) = magic == 0x00981B0787374E72 ;
 
 predicate plus_mult_overflow{L}(size_t a, size_t b) =
    (a != 0 && b != 0 && a > SIZE_MAX / 2) ||
    (a != 0 && b != 0 && b > SIZE_MAX / 2) ||
    (0 < a <= SIZE_MAX / 2 &&
     0 < b <= SIZE_MAX / 2 &&
     (a + b) > (SIZE_MAX / (a < b ? a : b))) ;
 
 predicate array_unchanged{L,T}(void *a, int c, int64_t n) =
    (c == GB_INT32_code  ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((int32_t*)a)[k],L) == \at(((int32_t*)a)[k],T))
        : \false
    ) ;
 
 predicate array_cast{L,T}(void *c, void *a, int c1, int c2, int64_t n) =
    (c1 == c2 == GB_INT32_code  ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((int32_t*)c)[k],L) == \at(((int32_t*)a)[k],T))
        : \false
    ) ;
 */

/*
 predicate array_unchanged{L,T}(void *a, int c, int64_t n) =
    (c == GB_BOOL_code   ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((bool*)a)[k],L) == \at(((bool*)a)[k],T))         :
    (c == GB_INT8_code   ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((int8_t*)a)[k],L) == \at(((int8_t*)a)[k],T))      :
    (c == GB_UINT8_code  ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((uint8_t*)a)[k],L) == \at(((uint8_t*)a)[k],T))   :
    (c == GB_INT16_code  ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((int16_t*)a)[k],L) == \at(((int16_t*)a)[k],T))   :
    (c == GB_UINT16_code ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((uint16_t*)a)[k],L) == \at(((uint16_t*)a)[k],T)) :
    (c == GB_INT32_code  ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((int32_t*)a)[k],L) == \at(((int32_t*)a)[k],T))   :
    (c == GB_UINT32_code ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((uint32_t*)a)[k],L) == \at(((uint32_t*)a)[k],T)) :
    (c == GB_INT64_code  ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((int64_t*)a)[k],L) == \at(((int64_t*)a)[k],T))   :
    (c == GB_UINT64_code ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((uint64_t*)a)[k],L) == \at(((uint64_t*)a)[k],T)) :
    (c == GB_FP32_code   ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((float*)a)[k],L) == \at(((float*)a)[k],T))       :
    (c == GB_FP64_code   ?
        (\forall int64_t k; 0 <= k < n ==>
            \at(((double*)a)[k],L) == \at(((double*)a)[k],T))     :
        \false
    ))))))))))) ;
 
 predicate array_cast{L,T}(void *c, void *a, int c1, int c2, int64_t n) =
    (c1 == GB_BOOL_code   ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == \at(((bool*)a)[k],T))           :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((float*)a)[k],T))    :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((bool*)c)[k],L) == (bool)\at(((double*)a)[k],T))   :
            \false
        ))))))))))) :
    (c1 == GB_INT8_code   ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == \at(((int8_t*)a)[k],T))           :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int8_t*)c)[k],L) == (int8_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((int8_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((int8_t*)c)[k],L) == INT8_MAX :
                                \at(((int8_t*)c)[k],L) == INT8_MIN
                            ) :
                            \at(((int8_t*)c)[k],L) == ((int8_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((int8_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((int8_t*)c)[k],L) == INT8_MAX :
                                \at(((int8_t*)c)[k],L) == INT8_MIN
                            ) :
                            \at(((int8_t*)c)[k],L) == ((int8_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_UINT8_code  ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == \at(((uint8_t*)a)[k],T))           :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint8_t*)c)[k],L) == (uint8_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((uint8_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((uint8_t*)c)[k],L) == UINT8_MAX :
                                \at(((uint8_t*)c)[k],L) == 0
                            ) :
                            \at(((uint8_t*)c)[k],L) == ((uint8_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((uint8_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((uint8_t*)c)[k],L) == UINT8_MAX :
                                \at(((uint8_t*)c)[k],L) == 0
                            ) :
                            \at(((uint8_t*)c)[k],L) == ((uint8_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_INT16_code  ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == \at(((int16_t*)a)[k],T))           :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int16_t*)c)[k],L) == (int16_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((int16_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((int16_t*)c)[k],L) == INT16_MAX :
                                \at(((int16_t*)c)[k],L) == INT16_MIN
                            ) :
                            \at(((int16_t*)c)[k],L) == ((int16_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((int16_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((int16_t*)c)[k],L) == INT16_MAX :
                                \at(((int16_t*)c)[k],L) == INT16_MIN
                            ) :
                            \at(((int16_t*)c)[k],L) == ((int16_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_UINT16_code ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == \at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint16_t*)c)[k],L) == (uint16_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((uint16_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((uint16_t*)c)[k],L) == UINT16_MAX :
                                \at(((uint16_t*)c)[k],L) == 0
                            ) :
                            \at(((uint16_t*)c)[k],L) == ((uint16_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((uint16_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((uint16_t*)c)[k],L) == UINT16_MAX :
                                \at(((uint16_t*)c)[k],L) == 0
                            ) :
                            \at(((uint16_t*)c)[k],L) == ((uint16_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_INT32_code  ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == \at(((int32_t*)a)[k],T))           :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int32_t*)c)[k],L) == (int32_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((int32_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((int32_t*)c)[k],L) == INT32_MAX :
                                \at(((int32_t*)c)[k],L) == INT32_MIN
                            ) :
                            \at(((int32_t*)c)[k],L) == ((int32_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((int32_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((int32_t*)c)[k],L) == INT32_MAX :
                                \at(((int32_t*)c)[k],L) == INT32_MIN
                            ) :
                            \at(((int32_t*)c)[k],L) == ((int32_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_UINT32_code ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == \at(((uint32_t*)a)[k],T))           :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint32_t*)c)[k],L) == (uint32_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((uint32_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((uint32_t*)c)[k],L) == UINT32_MAX :
                                \at(((uint32_t*)c)[k],L) == 0
                            ) :
                            \at(((uint32_t*)c)[k],L) == ((uint32_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((uint32_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((uint32_t*)c)[k],L) == UINT32_MAX :
                                \at(((uint32_t*)c)[k],L) == 0
                            ) :
                            \at(((uint32_t*)c)[k],L) == ((uint32_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_INT64_code  ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == \at(((int64_t*)a)[k],T))           :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((int64_t*)c)[k],L) == (int64_t)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((int64_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((int64_t*)c)[k],L) == INT64_MAX :
                                \at(((int64_t*)c)[k],L) == INT64_MIN
                            ) :
                            \at(((int64_t*)c)[k],L) == ((int64_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((int64_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((int64_t*)c)[k],L) == INT64_MAX :
                                \at(((int64_t*)c)[k],L) == INT64_MIN
                            ) :
                            \at(((int64_t*)c)[k],L) == ((int64_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_UINT64_code ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == (uint64_t)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((uint64_t*)c)[k],L) == \at(((uint64_t*)a)[k],T))           :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((float*)a)[k],T)) ?
                        \at(((uint64_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((float*)a)[k],T)) ?
                            (\at(((float*)a)[k],T) > 0 ?
                                \at(((uint64_t*)c)[k],L) == UINT64_MAX :
                                \at(((uint64_t*)c)[k],L) == 0
                            ) :
                            \at(((uint64_t*)c)[k],L) == ((uint64_t)\at(((float*)a)[k],T))
                        )
                    )
            ) :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                    (\is_NaN(\at(((double*)a)[k],T)) ?
                        \at(((uint64_t*)c)[k],L) == 0 :
                        (\is_infinite(\at(((double*)a)[k],T)) ?
                            (\at(((double*)a)[k],T) > 0 ?
                                \at(((uint64_t*)c)[k],L) == UINT64_MAX :
                                \at(((uint64_t*)c)[k],L) == 0
                            ) :
                            \at(((uint64_t*)c)[k],L) == ((uint64_t)\at(((double*)a)[k],T))
                        )
                    )
            ) :
            \false
        ))))))))))) :
    (c1 == GB_FP32_code   ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == \at(((float*)a)[k],T))           :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((float*)c)[k],L) == (float)\at(((double*)a)[k],T))   :
            \false
        ))))))))))) :
    (c1 == GB_FP64_code   ?
        (c2 == GB_BOOL_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((bool*)a)[k],T))     :
        (c2 == GB_INT8_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((int8_t*)a)[k],T))   :
        (c2 == GB_UINT8_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((uint8_t*)a)[k],T))  :
        (c2 == GB_INT16_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((int16_t*)a)[k],T))  :
        (c2 == GB_UINT16_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((uint16_t*)a)[k],T)) :
        (c2 == GB_INT32_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((int32_t*)a)[k],T))  :
        (c2 == GB_UINT32_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((uint32_t*)a)[k],T)) :
        (c2 == GB_INT64_code  ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((int64_t*)a)[k],T))  :
        (c2 == GB_UINT64_code ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((uint64_t*)a)[k],T)) :
        (c2 == GB_FP32_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == (double)\at(((float*)a)[k],T))    :
        (c2 == GB_FP64_code   ?
            (\forall int64_t k; 0 <= k < n ==>
                \at(((double*)c)[k],L) == \at(((double*)a)[k],T))           :
            \false
        ))))))))))) :
        \false
    ))))))))))) ;
 */

//------------------------------------------------------------------------------
// GrB_Type
//------------------------------------------------------------------------------

// no footprint
/*@
 logic int type_code{L}(GrB_Type t) = t->code ;
 
 logic size_t type_size{L}(GrB_Type t) = t->size ;
 
 // ignore user defined types by returning 0; don't know size of user
 // defined types without full GrB_Type; this is used
 // where the Type code is available only
 logic size_t type_size{L}(int c) =
    (c == GB_BOOL_code   ?
        (size_t)sizeof(bool)     :
    (c == GB_INT8_code   ?
        (size_t)sizeof(int8_t)   :
    (c == GB_UINT8_code  ?
        (size_t)sizeof(uint8_t)  :
    (c == GB_INT16_code  ?
        (size_t)sizeof(int16_t)  :
    (c == GB_UINT16_code ?
        (size_t)sizeof(uint16_t) :
    (c == GB_INT32_code  ?
        (size_t)sizeof(int32_t)  :
    (c == GB_UINT32_code ?
        (size_t)sizeof(uint32_t) :
    (c == GB_INT64_code  ?
        (size_t)sizeof(int64_t)  :
    (c == GB_UINT64_code ?
        (size_t)sizeof(uint64_t) :
    (c == GB_FP32_code   ?
        (size_t)sizeof(float)    :
    (c == GB_FP64_code   ?
        (size_t)sizeof(double)   :
        (size_t)0
    ))))))))))) ;
 
 predicate type_code_compatible{L,T}(int c1, int c2) =
    ((c1 == GB_UDT_code || c2 == GB_UDT_code) ?
        c1 == c2 : true
    ) ;
 
 predicate type_compatible{L,T}(GrB_Type t1, GrB_Type t2) =
    ((type_code{L}(t1) == GB_UDT_code || type_code{T}(t2) == GB_UDT_code) ?
        t1 == t2 : true
    ) ;
 
 predicate type_init{L}(GrB_Type t) = magic_valid(t->magic) ;
 */

 /*
  // Slow for discharging proofs with Alt-ergo particularly when negated
  predicate type_code_valid{L}(GrB_Type t) =
    type_code(t) == GB_BOOL_code   ||
    type_code(t) == GB_INT8_code   ||
    type_code(t) == GB_UINT8_code  ||
    type_code(t) == GB_INT16_code  ||
    type_code(t) == GB_UINT16_code ||
    type_code(t) == GB_INT32_code  ||
    type_code(t) == GB_UINT32_code ||
    type_code(t) == GB_INT64_code  ||
    type_code(t) == GB_UINT64_code ||
    type_code(t) == GB_FP32_code   ||
    type_code(t) == GB_FP64_code   ||
    type_code(t) == GB_UDT_code ;
  
  // Alt-ergo has problems discharging proofs fast using this predicate defined
  // this way - particularly when negation occurs
  predicate type_size_valid{L}(GrB_Type t) =
    type_size(t) != 0 &&
    (type_code(t) == GB_BOOL_code ?
        type_size(t) == sizeof(bool) :
    (type_code(t) == GB_INT8_code ?
        type_size(t) == sizeof(int8_t) :
    (type_code(t) == GB_UINT8_code ?
        type_size(t) == sizeof(uint8_t) :
    (type_code(t) == GB_INT16_code ?
        type_size(t) == sizeof(int16_t) :
    (type_code(t) == GB_UINT16_code ?
        type_size(t) == sizeof(uint16_t) :
    (type_code(t) == GB_INT32_code ?
        type_size(t) == sizeof(int32_t) :
    (type_code(t) == GB_UINT32_code ?
        type_size(t) == sizeof(uint32_t) :
    (type_code(t) == GB_INT64_code ?
        type_size(t) == sizeof(int64_t) :
    (type_code(t) == GB_UINT64_code ?
        type_size(t) == sizeof(uint64_t) :
    (type_code(t) == GB_FP32_code ?
        type_size(t) == sizeof(float) :
    (type_code(t) == GB_FP64_code ?
        type_size(t) == sizeof(double) :
    (type_code(t) == GB_UDT_code ?
        type_size(t) == type_size(t) :
        \false
    )))))))))))) ;
 */
 
 /*@
  predicate type_code_valid{L}(GrB_Type t) =
    GB_BOOL_code <= type_code(t) <= GB_UDT_code ;
  
  predicate type_size_valid{L}(GrB_Type t) =
    type_size(t) != 0  &&
    type_code_valid(t) &&
    (type_code(t) == GB_BOOL_code   ==> type_size(t) == sizeof(bool))     &&
    (type_code(t) == GB_INT8_code   ==> type_size(t) == sizeof(int8_t))   &&
    (type_code(t) == GB_UINT8_code  ==> type_size(t) == sizeof(uint8_t))  &&
    (type_code(t) == GB_INT16_code  ==> type_size(t) == sizeof(int16_t))  &&
    (type_code(t) == GB_UINT16_code ==> type_size(t) == sizeof(uint16_t)) &&
    (type_code(t) == GB_INT32_code  ==> type_size(t) == sizeof(int32_t))  &&
    (type_code(t) == GB_UINT32_code ==> type_size(t) == sizeof(uint32_t)) &&
    (type_code(t) == GB_INT64_code  ==> type_size(t) == sizeof(int64_t))  &&
    (type_code(t) == GB_UINT64_code ==> type_size(t) == sizeof(uint64_t)) &&
    (type_code(t) == GB_FP32_code   ==> type_size(t) == sizeof(float))    &&
    (type_code(t) == GB_FP64_code   ==> type_size(t) == sizeof(double))   &&
    (type_code(t) == GB_UDT_code    ==> type_size(t) == type_size(t)) ;
 */

/*@
 predicate type_valid{L}(GrB_Type t) =
    \valid(t) &&
    type_init(t) &&
    type_code_valid(t) &&
    type_size_valid(t) ;
 */


/* TODO[MAYBE]: Equality */

//------------------------------------------------------------------------------
// GrB_BinaryOp
//------------------------------------------------------------------------------

/*@
 logic void* binaryop_func{L}(GrB_BinaryOp o) = o->function ;
 
 logic int binaryop_code{L}(GrB_BinaryOp o) = o->opcode ;
 
 logic GrB_Type binaryop_outtype{L}(GrB_BinaryOp o) = o->ztype ;
 
 logic GrB_Type binaryop_in1type{L}(GrB_BinaryOp o) = o->xtype ;
 
 logic GrB_Type binaryop_in2type{L}(GrB_BinaryOp o) = o->ytype ;
 
 logic set<char*> binaryop_fp{L}(GrB_BinaryOp o) =
    \union(o,
           (char*)(o->function),
           o->ztype,
           o->xtype,
           o->ytype) ;
 
 predicate binaryop_init{L}(GrB_BinaryOp o) = magic_valid(o->magic) ;
 
 predicate binaryop_code_valid{L}(GrB_BinaryOp o) =
    GB_FIRST_opcode <= binaryop_code(o) <= GB_USER_opcode ;
 
 // used in monoid validity, assumes o is valid binaryop
 // ie. binaryop_valid(o) == \true
 predicate binaryop_domains_same{L}(GrB_BinaryOp o) =
    binaryop_outtype(o) == binaryop_in1type(o) == binaryop_in2type(o) ;
 
 predicate binaryop_fp_separated{L}(GrB_BinaryOp o) =
    \separated(o,
               (char*)(o->function),
               o->ztype) &&
    \separated(o,
               (char*)(o->function),
               o->xtype) &&
    \separated(o,
               (char*)(o->function),
               o->ytype) ;
 */

/*@
 predicate binaryop_valid{L}(GrB_BinaryOp o) =
    \valid(o) &&
    binaryop_init(o) &&
    binaryop_func(o) != \null &&
    binaryop_code_valid(o) &&
    type_valid(binaryop_outtype(o)) &&
    type_valid(binaryop_in1type(o)) &&
    type_valid(binaryop_in2type(o)) &&
    binaryop_fp_separated(o) ;
 */

/* TODO[MAYBE]: Equality */

//------------------------------------------------------------------------------
// GrB_Info
//------------------------------------------------------------------------------

// GrB_Info is an enum type

/*@
 predicate info_valid(GrB_Info i) =
    i == GrB_SUCCESS              ||
    i == GrB_NO_VALUE             ||
    i == GrB_UNINITIALIZED_OBJECT ||
    i == GrB_INVALID_OBJECT       ||
    i == GrB_NULL_POINTER         ||
    i == GrB_INVALID_VALUE        ||
    i == GrB_INVALID_INDEX        ||
    i == GrB_DOMAIN_MISMATCH      ||
    i == GrB_DIMENSION_MISMATCH   ||
    i == GrB_OUTPUT_NOT_EMPTY     ||
    i == GrB_OUT_OF_MEMORY        ||
    i == GrB_INSUFFICIENT_SPACE   ||
    i == GrB_INDEX_OUT_OF_BOUNDS  ||
    i == GrB_PANIC ;
 */

//------------------------------------------------------------------------------
// GrB_Descriptor
//------------------------------------------------------------------------------

// no footprint -- GrB_Desc_Value is an enum type not a pointer type

/*@
 logic GrB_Desc_Value descriptor_output{L}(GrB_Descriptor d) = d->out ;
 
 logic GrB_Desc_Value descriptor_mask{L}(GrB_Descriptor d) = d->mask ;
 
 logic GrB_Desc_Value descriptor_input0{L}(GrB_Descriptor d) = d->in0 ;
 
 logic GrB_Desc_Value descriptor_input1{L}(GrB_Descriptor d) = d->in1 ;
 
 predicate descriptor_init{L}(GrB_Descriptor d) = magic_valid(d->magic) ;
 
 // nondefault should be the valid nondefault GrB_Desc_Value that v should be
 predicate descriptor_value_valid(GrB_Desc_Value v, GrB_Desc_Value nondefault) =
    v == GxB_DEFAULT || v == nondefault ;
 */

/*@
 predicate descriptor_valid{L}(GrB_Descriptor d) =
    \valid(d) &&
    descriptor_init(d) &&
    descriptor_value_valid(descriptor_output(d), GrB_REPLACE) &&
    descriptor_value_valid(descriptor_mask(d), GrB_SCMP) &&
    descriptor_value_valid(descriptor_input0(d), GrB_TRAN) &&
    descriptor_value_valid(descriptor_input1(d), GrB_TRAN) ;
 */
 
/* TODO[MAYBE]: Equality */

//------------------------------------------------------------------------------
// GrB_Monoid
//------------------------------------------------------------------------------

/* TODO: specification validity for monoid not already checked - binaryop is
         associative, identity is in fact an identity element of the binaryop &
         domain, other algebraic properties of a monoid not checked
 */

/*@
 logic GrB_BinaryOp monoid_op{L}(GrB_Monoid m) = m->op ;
 
 logic void* monoid_identity{L}(GrB_Monoid m) = m->identity ;
 
 logic set<char*> monoid_fp{L}(GrB_Monoid m) =
    \union(m,
           m->op,
           ((char*)m->identity) + (0..(m->op->ztype->size)-1)) ;
 
 predicate monoid_init{L}(GrB_Monoid m) = magic_valid(m->magic) ;
 
 // assumes the monoid's binary op is valid,
 // ie. binaryop_valid(monoid_op(m)) == \true
 // assumes the monoid's identity element can be deferenced
 // ie. \valid(((char*)monoid_identity(m)) +
 //         (0..(type_size(binaryop_outtype(monoid_op(m))))-1)) == \true
 // internal predicate of monoid_valid
 predicate identity_is_zero_bool_valid{L}(GrB_Monoid m) =
    (m->identity_is_zero == \true ?
        (\forall int64_t k; 0 <= k < type_size(binaryop_outtype(monoid_op(m)))
            ==> ((int8_t*)monoid_identity(m))[k] == 0
        ) :
        !(\forall int64_t k; 0 <= k < type_size(binaryop_outtype(monoid_op(m)))
            ==> ((int8_t*)monoid_identity(m))[k] == 0
         )
    ) ;
 
 predicate monoid_fp_separated{L}(GrB_Monoid m) =
    \separated(m,
               m->op,
               ((char*)m->identity) + (0..(m->op->ztype->size)-1)) ;
 */

/*@
 predicate monoid_valid{L}(GrB_Monoid m) =
    \valid(m) &&
    monoid_init(m) &&
    binaryop_valid(monoid_op(m)) &&
    binaryop_domains_same(monoid_op(m)) &&
    \valid(((char*)monoid_identity(m)) +
        (0..(type_size(binaryop_outtype(monoid_op(m))))-1)) &&
    identity_is_zero_bool_valid(m) &&
    monoid_fp_separated(m) ;
 */

/* TODO[MAYBE]: Equality */

//------------------------------------------------------------------------------
// GrB_Semiring
//------------------------------------------------------------------------------

/* TODO: check that a valid semiring's monoid is commutative */

/*@
 logic GrB_Monoid semiring_monoid{L}(GrB_Semiring s) = s->add ;
 
 // assumes that s->add is a valid monoid, ie. monoid_valid(s->add) == \true
 logic GrB_BinaryOp semiring_add{L}(GrB_Semiring s) = s->add->op ;
 
 logic GrB_BinaryOp semiring_mult{L}(GrB_Semiring s) = s->multiply ;
 
 logic set<char*> semiring_fp{L}(GrB_Semiring s) =
    \union(s,
           s->add,
           s->multiply) ;
 
 predicate semiring_init{L}(GrB_Semiring s) = magic_valid(s->magic) ;
 
 predicate semiring_fp_separated{L}(GrB_Semiring s) =
    \separated(s,
               s->add,
               s->multiply) ;
 */

/*@
 // might expose too much in implementation details
 predicate semiring_valid{L}(GrB_Semiring s) =
    \valid(s) &&
    semiring_init(s) &&
    monoid_valid(semiring_monoid(s)) &&
    binaryop_valid(semiring_mult(s)) &&
    binaryop_outtype(semiring_mult(s)) ==
        binaryop_outtype(semiring_add(s)) &&
    semiring_fp_separated(s) ;
 */

/* TODO[MAYBE]: Equality */

//------------------------------------------------------------------------------
// GrB_Matrix
//------------------------------------------------------------------------------

/*@
 logic int64_t matrix_nrows{L}(GrB_Matrix m) = m->nrows ;
 
 logic int64_t matrix_ncols{L}(GrB_Matrix m) = m->ncols ;
 
 logic int64_t matrix_nvals{L}(GrB_Matrix m) = m->nzmax ;
 
 logic GrB_Type matrix_type{L}(GrB_Matrix m) = m->type ;
 
 logic int64_t nnz{L}(GrB_Matrix m) = ((matrix_nvals(m) > 0) ? (m->p)[matrix_ncols(m)] : (int64_t)0) ;
 
 logic set<char*> matrix_fp{L}(GrB_Matrix m) =
    \union(m,
           m->type,
           (((char*)m->p) + (0..sizeof(int64_t)-1)) + (0..(m->ncols+1)-1),
           (((char*)m->i) + (0..sizeof(int64_t)-1)) + (0..(m->nzmax)-1),
           ((char*)(m->x + (0..(m->nzmax)-1))) + (0..(m->type->size)-1),
           (((char*)m->ipending) + (0..sizeof(int64_t)-1)) + (0..(m->max_npending)-1),
           (((char*)m->jpending) + (0..sizeof(int64_t)-1)) + (0..(m->max_npending)-1),
           ((char*)(m->xpending + (0..(m->max_npending)-1))) + (0..(m->type->size)-1),
           m->operator_pending,
           ((GrB_Matrix)m->queue_next),
           ((GrB_Matrix)m->queue_prev)) ;
 
 predicate matrix_init{L}(GrB_Matrix m) = magic_valid(m->magic) ;
 
 // helper function for row_indices_valid predicate
 logic int64_t unflip(int64_t i) = (i < 0) ? (int64_t)((-i)-2) : i ;
 
 // check row indices in bounds, no duplicates, and ensure sorted
 predicate row_indices_valid{L}(GrB_Matrix m) =
    \valid(m->p + (0..(matrix_ncols(m)+1)-1))
    &&
    \valid(m->i + (0..(matrix_nvals(m))-1))
    &&
    (\forall int64_t j; 0 <= j < matrix_ncols(m) ==>
        in_bounds :
            (\forall int64_t p; (m->p)[j] <= p < (m->p)[j+1] ==>
                0 <= unflip((m->i)[p]) < matrix_nrows(m)
            )
        &&
        sorted_no_dups :
            (\forall int64_t p; (m->p)[j] <= p < (m->p)[j+1]-1 ==>
                unflip((m->i)[p]) < unflip((m->i)[p+1])
            )
    ) ;
 
 // internal predicate to matrix_storage_valid
 // not to be called directly
 predicate pending_tuples_valid{L}(GrB_Matrix m) =
    0 <= m->max_npending
    &&
    0 <= m->npending <= m->max_npending
    &&
    (m->npending == 0 ?
        (m->xpending != \null || m->ipending != \null ||
         m->jpending != \null || m->max_npending != 0 ?
            \false : \true
        ) :
        ((m->xpending == \null || m->ipending == \null ||
         (matrix_ncols(m) > 1 && m->jpending == \null) ?
            \false : \true)
         &&
         \valid(m->ipending + (0..(m->max_npending)-1))
         &&
         \valid(m->jpending + (0..(m->max_npending)-1))
         &&
         \valid(((char*)(m->xpending)) + (0..((m->max_npending)*type_size(matrix_type(m)))-1))
         &&
         tuple_indices_in_bounds :
            (\forall int64_t k; 0 <= k < m->npending ==>
                (0 <= (m->ipending)[k] < matrix_nrows(m)) &&
                (0 <= (matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k])) < matrix_ncols(m))
            )
         &&
         tuple_indices_sorted :
            (m->sorted_pending == 1 ?
                (\forall int64_t k; 0 <= k < m->npending-1 ==>
                    ((matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k])) <
                        (matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k+1]))
                    ) ||
                    ((matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k])) ==
                        (matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k+1]))
                      &&
                     ((m->ipending)[k] <= (m->ipending)[k+1])
                    )
                ) :
                !(\forall int64_t k; 0 <= k < m->npending-1 ==>
                    ((matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k])) <
                        (matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k+1]))
                    ) ||
                    ((matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k])) ==
                        (matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k+1]))
                      &&
                     ((m->ipending)[k] <= (m->ipending)[k+1])
                    )
                )
            )
         &&
         operator_pending_valid :
            (m->operator_pending == \null ?
                \true :
                binaryop_valid(m->operator_pending)
            )
        )
    ) ;
 
 // check p, i, x, pix pendings, zombies, and matrix queue (sort of for the queue)
 predicate matrix_storage_valid{L}(GrB_Matrix m) =
    \valid(m->p + (0..(matrix_ncols(m)+1)-1))
    &&
    (matrix_nvals(m) == 0 ?
        (m->x != \null || m->i != \null || m->i_shallow == 1 || m->x_shallow == 1 ?
            \false :
            (col_ptrs_valid :
                \forall int64_t j; 0 <= j < matrix_ncols(m) ==> (m->p)[j] == 0
            )
        ) :
        (m->x == \null || m->i == \null ?
            \false :
            (m->p)[0] == 0
            &&
            col_ptrs_valid :
                (\forall int64_t j; 0 <= j < matrix_ncols(m) ==>
                    (m->p)[j] <= (m->p)[j+1] <= matrix_nvals(m)
                )
            &&
            \valid(((char*)(m->x)) + (0..(matrix_nvals(m)*type_size(matrix_type(m)))-1))
            &&
            row_indices_valid(m)
        )
    )
    &&
    0 <= m->nzombies <= (m->p)[matrix_ncols(m)]
    &&
    pending_tuples_valid(m)
    &&
    (m->enqueued == 0 ?
        (m->queue_next == \null &&
         m->queue_prev == \null
        ) :
        \true
    ) ;
 
 // call only at end of matrix valid predicate
 predicate matrix_fp_separated{L}(GrB_Matrix m) =
    \separated(m,
               m->type,
               m->p + (0..(m->ncols+1)-1),
               \union(((char*)(m->i)) +
                        (0..(m->i == \null ? 0 : (m->nzmax)*sizeof(int64_t))-1),
                      ((char*)(m->x)) +
                        (0..(m->x == \null ? 0 : (m->nzmax)*(m->type->size))-1),
                      ((char*)(m->ipending)) +
                        (0..(m->ipending == \null ? 0 : (m->max_npending)*sizeof(int64_t))-1),
                      ((char*)(m->jpending)) +
                        (0..(m->jpending == \null ? 0 : (m->max_npending)*sizeof(int64_t))-1),
                      ((char*)(m->xpending)) +
                        (0..(m->xpending == \null ? 0 : (m->max_npending)*(m->type->size))-1),
                      m->operator_pending,
                      ((GrB_Matrix)m->queue_next),
                      ((GrB_Matrix)m->queue_prev)
                     )
              )
    &&
    (m->i != \null && m->x != \null ==>
        \separated(m->i + (0..(m->nzmax)-1),
                   ((char*)(m->x)) + (0..((m->nzmax)*(m->type->size))-1),
                   \union(((char*)(m->ipending)) +
                            (0..(m->ipending == \null ? 0 : (m->max_npending)*sizeof(int64_t))-1),
                          ((char*)(m->jpending)) +
                            (0..(m->jpending == \null ? 0 : (m->max_npending)*sizeof(int64_t))-1),
                          ((char*)(m->xpending)) +
                            (0..(m->xpending == \null ? 0 : (m->max_npending)*(m->type->size))-1),
                          m->operator_pending,
                          ((GrB_Matrix)m->queue_next),
                          ((GrB_Matrix)m->queue_prev)
                         )
                  )
    )
    &&
    (m->ipending != \null && m->xpending != \null ==>
        \separated(m->ipending + (0..(m->max_npending)-1),
                   ((char*)(m->xpending)) + (0..((m->max_npending)*(m->type->size))-1),
                   \union(((char*)(m->jpending)) +
                            (0..(m->jpending == \null ? 0 : (m->max_npending)*sizeof(int64_t))-1),
                          m->operator_pending,
                          ((GrB_Matrix)m->queue_next),
                          ((GrB_Matrix)m->queue_prev)
                         )
                  )
    )
    &&
    (m->jpending != \null ==>
        \separated(m->jpending + (0..(m->max_npending)-1),
                   \union(m->operator_pending,
                          ((GrB_Matrix)m->queue_next),
                          ((GrB_Matrix)m->queue_prev)
                         )
                  )
    )
    &&
    (m->operator_pending != \null ==>
        \separated(m->operator_pending,
                   \union(((GrB_Matrix)m->queue_next),
                          ((GrB_Matrix)m->queue_prev)
                         )
                  )
    )
    &&
    (m->queue_next != \null || m->queue_prev != \null ==>
        \separated(((GrB_Matrix)m->queue_next),
                   ((GrB_Matrix)m->queue_prev))
    ) ;
 
 predicate matrix_malloc_init{L}(GrB_Matrix m) = m->magic == 0x10981B0787374E72 ;
 
 predicate freeable_storage{L}(GrB_Matrix m) =
    (m->p_shallow == 0 && m->p != \null ==> \freeable(m->p)) &&
    (m->i_shallow == 0 && m->i != \null ==> \freeable(m->i)) &&
    (m->x_shallow == 0 && m->x != \null ==> \freeable(m->x)) &&
    (m->ipending != \null ==> \freeable(m->ipending)) &&
    (m->jpending != \null ==> \freeable(m->jpending)) &&
    (m->xpending != \null ==> \freeable(m->xpending)) ;
 
 // valid matrix except for column array being allocated but not initialized
 // m->p_shallow will most likely be false if this is true, but not necessarily
 predicate matrix_malloc_valid{L}(GrB_Matrix m) =
    \valid(m)                                 &&
    matrix_malloc_init(m)                     &&
    0 < matrix_nrows(m) <= (1ULL << 60)       &&
    0 < matrix_ncols(m) <= (1ULL << 60)       &&
    type_valid(matrix_type(m))                &&
    \valid(m->p + (0..(matrix_ncols(m)+1)-1)) &&
    matrix_nvals(m) == 0                      &&
    m->i == \null                             &&
    m->x == \null                             &&
    m->i_shallow == 0                         &&
    m->x_shallow == 0                         &&
    m->nzombies == 0                          &&
    pending_tuples_valid(m)                   &&
    (m->enqueued == 0 ?
        (m->queue_next == \null &&
         m->queue_prev == \null
        ) :
        \true
    )                                         &&
    matrix_fp_separated(m) ;
 
 // doesn't include p, because p may be null, allocated but not initialized,
 // or both allocated and initialized by the end of the call to GB_new
 predicate matrix_storage_init{L}(GrB_Matrix m) =
    \valid(m)                    &&
    matrix_nvals(m) == 0         &&
    m->i == \null                &&
    m->x == \null                &&
    m->p_shallow == 0            &&
    m->i_shallow == 0            &&
    m->x_shallow == 0            &&
    m->npending == 0             &&
    m->max_npending == 0         &&
    m->sorted_pending == 1       &&
    m->operator_pending == \null &&
    m->ipending == \null         &&
    m->jpending == \null         &&
    m->xpending == \null         &&
    m->queue_next == \null       &&
    m->queue_prev == \null       &&
    m->enqueued == 0             &&
    m->nzombies == 0 ;
 */

/*@
 // nrows, ncols should be >0 by spec, but implementation check says >=0
 predicate matrix_valid{L}(GrB_Matrix m) =
    \valid(m) &&
    matrix_init(m) &&
    0 < matrix_nrows(m) <= (1ULL << 60) &&
    0 < matrix_ncols(m) <= (1ULL << 60) &&
    0 <= matrix_nvals(m) <= (1ULL << 60) &&
    type_valid(matrix_type(m)) &&
    matrix_storage_valid(m) &&
    matrix_fp_separated(m) ;
 */

/* TODO: Queue linked list verification -- reachability predicates, etc.
         -- validity of matrix object linked-list part -- in the queue when it
         should be, not in the queue when it shouldn't be, etc. to validate other
         parts of internal rep of matrix
 */

/* TODO [MAYBE]: not checking for correct number of zombie indices when checking
                 row indices requires ghost code -- for matrix valid
 */

/* TODO: Equality */

//------------------------------------------------------------------------------
// GrB_Vector
//------------------------------------------------------------------------------

/*@
 logic int64_t vector_nrows{L}(GrB_Vector v) = v->nrows ;
 
 logic int64_t vector_ncols{L}(GrB_Vector v) = v->ncols ;
 
 logic int64_t vector_nvals{L}(GrB_Vector v) = v->nzmax ;
 
 logic GrB_Type vector_type{L}(GrB_Vector v) = v->type ;
 
 logic set<char*> vector_fp{L}(GrB_Vector v) = matrix_fp((GrB_Matrix)v) ;
 */

/*@
 predicate vector_valid{L}(GrB_Vector v) =
    matrix_valid((GrB_Matrix)v) &&
    vector_ncols(v) == 1 ;
 */
