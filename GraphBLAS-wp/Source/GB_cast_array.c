//------------------------------------------------------------------------------
// GB_cast_array: typecast an array
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA CHANGE 6/25/18 ***
// Changed use of CAST macro definition to match new CAST macro definition
// Changed WORKER macro definition to include the type codes for new CAST macro def

// *** JENNA ANNOTATION 8/4/18 ***
// GB_cast_array

//------------------------------------------------------------------------------

// Casts an input array A to an output array C with a different built-in type.
// Does not handle user-defined types.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 behavior n_zero :
    assumes n == 0 ;
    assigns \nothing ;
    ensures n == 0 ;
 
 behavior n_not_zero :
    assumes n != 0 ;
 
    requires n > 0 ;
    requires code1 < GB_UDT_code ;
    requires code2 < GB_UDT_code ;
    requires type_code_compatible{Here,Here}((int)code1,(int)code2) ;
    requires \valid((((char*)C) + (0..type_size((int)code1)-1)) + (0..n-1)) ;
    requires \valid((((char*)A) + (0..type_size((int)code2)-1)) + (0..n-1)) ;
    requires (!\separated((((char*)C) + (0..type_size((int)code1)-1)) + (0..n-1),
                          (((char*)A) + (0..type_size((int)code2)-1)) + (0..n-1)) ==>
                code1 == code2) ;
 
    assigns *((((char*)C) + (0..type_size((int)code1)-1)) + (0..n-1)) ;
 
    ensures array_unchanged{Pre,Here}(A,(int)code2,n) ;
    ensures array_cast{Here,Pre}(C,A,(int)code1,(int)code2,n) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
void GB_cast_array              // typecast an array
(
    void *C,                    // output array
    const GB_Type_code code1,   // type code for C
    const void *A,              // input array
    const GB_Type_code code2,   // type code for A
    const int64_t n             // number of entries in C and A
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    if (n == 0)
    {
        // no work to do, and the A and C pointer may be NULL as well
        return ;
    }

    ASSERT (C != NULL) ;
    ASSERT (A != NULL) ;
    ASSERT (n > 0) ;
    ASSERT (code1 < GB_UDT_code) ;
    ASSERT (code2 < GB_UDT_code) ;
    ASSERT (GB_Type_code_compatible (code1, code2)) ;

    //--------------------------------------------------------------------------
    // define the worker for the switch factory
    //--------------------------------------------------------------------------

    #define WORKER(ctype,atype,ccode,acode)                                     \
    {                                                                           \
        ctype *c = (ctype *) C ;                                                \
        atype *a = (atype *) A ;                                                \
                                                                                \
        /*@                                                                     \
         loop invariant 0 <= k <= n ;                                           \
         loop invariant array_unchanged{LoopEntry,Here}(a,(int)acode,k) ;       \
         loop invariant array_cast{Here,Here}(c,a,(int)ccode,(int)acode,k) ;    \
         loop assigns k, c[0..n-1] ;                                            \
         loop variant n - k ;                                                   \
        */                                                                      \
        for (int64_t k = 0 ; k < n ; k++)                                       \
        {                                                                       \
            /* c [k] = a [k] ; */                                               \
            CAST (c [k], a [k], ccode, acode) ;                                 \
        }                                                                       \
    }                                                                           \
    break ;

    //--------------------------------------------------------------------------
    // launch the switch factory
    //--------------------------------------------------------------------------

    // There is no generic worker so the switch factory cannot be disabled.
    #include "GB_2type_template.c"
    #undef WORKER
}

