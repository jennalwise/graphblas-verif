//------------------------------------------------------------------------------
// GB_2type_template.c: 2-type switch factory
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA CHANGE 6/25/18 ***
// Changed use of WORKER macro definition to match new WORKER macro definition

// *** JENNA CHANGE 8/5/18 ***
// Commented all workers out except for int32 to int32 for verification
// Needed to move worker macro code in directly for loop annotations; only done for int32 to int32

//------------------------------------------------------------------------------

// This is a generic switch factory for creating 121 workers that operate on
// two built-in data types (11 types each), to be #include'd in another file.
// WORKER(type1,type2) is a macro defined in the #including file, where type1
// and type2 are the built-in types corresponding to code1 and code2,
// respectively or (void *) for a user-defined type.  The last statement of
// WORKER should be a break or return since it doesn't appear here.

// User-defined types are not handled.

// GB_shallow_op and GB_transpose_op use this template to create workers that
// apply unary operators.  Those functions #define BOP(x) for the boolean
// unary operator, IOP(x) for integers, and FOP(x) for floating-point.  The
// selection of these operators is controlled by code1.

switch (code1)
{
    /*case GB_BOOL_code   :

        #define OP(x) BOP(x)
        switch (code2)
        {
            //                            code1 code2
            #ifndef NSAME
            case GB_BOOL_code   : WORKER (bool, bool, code1, code2)
            #endif
            case GB_INT8_code   : WORKER (bool, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (bool, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (bool, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (bool, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (bool, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (bool, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (bool, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (bool, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (bool, float, code1, code2)
            case GB_FP64_code   : WORKER (bool, double, code1, code2)
            default: ;
        }
        break ;
        #undef  OP

    case GB_INT8_code   :

        #define OP(x) IOP(x)
        switch (code2)
        {
            //                            code1   code2
            case GB_BOOL_code   : WORKER (int8_t, bool, code1, code2)
            #ifndef NSAME
            case GB_INT8_code   : WORKER (int8_t, int8_t, code1, code2)
            #endif
            case GB_UINT8_code  : WORKER (int8_t, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (int8_t, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (int8_t, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (int8_t, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (int8_t, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (int8_t, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (int8_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (int8_t, float, code1, code2)
            case GB_FP64_code   : WORKER (int8_t, double, code1, code2)
            default: ;
        }
        break ;

    case GB_UINT8_code  :

        switch (code2)
        {
            //                            code1    code2
            case GB_BOOL_code   : WORKER (uint8_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (uint8_t, int8_t, code1, code2)
            #ifndef NSAME
            case GB_UINT8_code  : WORKER (uint8_t, uint8_t, code1, code2)
            #endif
            case GB_INT16_code  : WORKER (uint8_t, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (uint8_t, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (uint8_t, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (uint8_t, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (uint8_t, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (uint8_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (uint8_t, float, code1, code2)
            case GB_FP64_code   : WORKER (uint8_t, double, code1, code2)
            default: ;
        }
        break ;

    case GB_INT16_code  :

        switch (code2)
        {
            //                            code1    code2
            case GB_BOOL_code   : WORKER (int16_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (int16_t, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (int16_t, uint8_t, code1, code2)
            #ifndef NSAME
            case GB_INT16_code  : WORKER (int16_t, int16_t, code1, code2)
            #endif
            case GB_UINT16_code : WORKER (int16_t, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (int16_t, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (int16_t, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (int16_t, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (int16_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (int16_t, float, code1, code2)
            case GB_FP64_code   : WORKER (int16_t, double, code1, code2)
            default: ;
        }
        break ;

    case GB_UINT16_code :

        switch (code2)
        {
            //                            code1     code2
            case GB_BOOL_code   : WORKER (uint16_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (uint16_t, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (uint16_t, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (uint16_t, int16_t, code1, code2)
            #ifndef NSAME
            case GB_UINT16_code : WORKER (uint16_t, uint16_t, code1, code2)
            #endif
            case GB_INT32_code  : WORKER (uint16_t, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (uint16_t, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (uint16_t, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (uint16_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (uint16_t, float, code1, code2)
            case GB_FP64_code   : WORKER (uint16_t, double, code1, code2)
            default: ;
        }
        break ;
     */
    case GB_INT32_code  :

        switch (code2)
        {
            //                            code1    code2
            /*case GB_BOOL_code   : WORKER (int32_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (int32_t, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (int32_t, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (int32_t, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (int32_t, uint16_t, code1, code2)
            */
            #ifndef NSAME
            case GB_INT32_code  :
                //WORKER (int32_t, int32_t, code1, code2)
                {
                    int32_t *c = (int32_t *) C ;
                    int32_t *a = (int32_t *) A ;
    
                    /*@
                     loop invariant 0 <= k <= n ;
                     loop invariant array_unchanged{LoopEntry,Here}(a,(int)code2,k) ;
                     loop invariant array_cast{Here,Here}(c,a,(int)code1,(int)code2,k) ;
                     loop assigns k, c[0..n-1] ;
                     loop variant n - k ;
                     */
                    for (int64_t k = 0 ; k < n ; k++)
                    {
                        /* c [k] = a [k] ; */
                        CAST (c [k], a [k], code1, code2) ;
                    }
                }
                break ;
            #endif
            /*case GB_UINT32_code : WORKER (int32_t, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (int32_t, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (int32_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (int32_t, float, code1, code2)
            case GB_FP64_code   : WORKER (int32_t, double, code1, code2)
            */
            default: ;
        }
        break ;

    /*case GB_UINT32_code :

        switch (code2)
        {
            //                            code1     code2
            case GB_BOOL_code   : WORKER (uint32_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (uint32_t, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (uint32_t, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (uint32_t, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (uint32_t, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (uint32_t, int32_t, code1, code2)
            #ifndef NSAME
            case GB_UINT32_code : WORKER (uint32_t, uint32_t, code1, code2)
            #endif
            case GB_INT64_code  : WORKER (uint32_t, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (uint32_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (uint32_t, float, code1, code2)
            case GB_FP64_code   : WORKER (uint32_t, double, code1, code2)
            default: ;
        }
        break ;

    case GB_INT64_code  :

        switch (code2)
        {
            //                            code1    code2
            case GB_BOOL_code   : WORKER (int64_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (int64_t, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (int64_t, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (int64_t, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (int64_t, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (int64_t, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (int64_t, uint32_t, code1, code2)
            #ifndef NSAME
            case GB_INT64_code  : WORKER (int64_t, int64_t, code1, code2)
            #endif
            case GB_UINT64_code : WORKER (int64_t, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (int64_t, float, code1, code2)
            case GB_FP64_code   : WORKER (int64_t, double, code1, code2)
            default: ;
        }
        break ;

    case GB_UINT64_code :

        switch (code2)
        {
            //                            code1     code2
            case GB_BOOL_code   : WORKER (uint64_t, bool, code1, code2)
            case GB_INT8_code   : WORKER (uint64_t, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (uint64_t, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (uint64_t, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (uint64_t, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (uint64_t, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (uint64_t, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (uint64_t, int64_t, code1, code2)
            #ifndef NSAME
            case GB_UINT64_code : WORKER (uint64_t, uint64_t, code1, code2)
            #endif
            case GB_FP32_code   : WORKER (uint64_t, float, code1, code2)
            case GB_FP64_code   : WORKER (uint64_t, double, code1, code2)
            default: ;
        }
        break ;
        #undef  OP

    case GB_FP32_code   :

        #define OP(x) FOP(x)
        switch (code2)
        {
            //                            code1  code2
            case GB_BOOL_code   : WORKER (float, bool, code1, code2)
            case GB_INT8_code   : WORKER (float, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (float, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (float, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (float, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (float, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (float, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (float, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (float, uint64_t, code1, code2)
            #ifndef NSAME
            case GB_FP32_code   : WORKER (float, float, code1, code2)
            #endif
            case GB_FP64_code   : WORKER (float, double, code1, code2)
            default: ;
        }
        break ;

    case GB_FP64_code   :

        switch (code2)
        {
            //                            code1   code2
            case GB_BOOL_code   : WORKER (double, bool, code1, code2)
            case GB_INT8_code   : WORKER (double, int8_t, code1, code2)
            case GB_UINT8_code  : WORKER (double, uint8_t, code1, code2)
            case GB_INT16_code  : WORKER (double, int16_t, code1, code2)
            case GB_UINT16_code : WORKER (double, uint16_t, code1, code2)
            case GB_INT32_code  : WORKER (double, int32_t, code1, code2)
            case GB_UINT32_code : WORKER (double, uint32_t, code1, code2)
            case GB_INT64_code  : WORKER (double, int64_t, code1, code2)
            case GB_UINT64_code : WORKER (double, uint64_t, code1, code2)
            case GB_FP32_code   : WORKER (double, float, code1, code2)
            #ifndef NSAME
            case GB_FP64_code   : WORKER (double, double, code1, code2)
            #endif
            default: ;
        }
        break ;
        #undef  OP
     */
    default: ;
}

#undef OP
#undef IOP
#undef FOP
#undef BOP
#undef NSAME

