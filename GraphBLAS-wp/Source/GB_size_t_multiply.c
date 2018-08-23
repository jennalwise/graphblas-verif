//------------------------------------------------------------------------------
// GB_size_t_multiply:  multiply two size_t and guard against overflow
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 7/29/18 ***
// GB_size_t_multiply

//------------------------------------------------------------------------------

// c = a*b but check for overflow

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires c != \null ;
 requires \valid(c) ;
 assigns *c ;
 behavior a_or_b_zero:
    assumes a == 0 || b == 0 ;
    ensures \result == 1 ;
    ensures *c == 0 ;
 behavior a_plus_b_not_safe:
    assumes a != 0 ;
    assumes b != 0 ;
    assumes (a > SIZE_MAX / 2 || b > SIZE_MAX / 2) ;
    ensures \result == 0 ;
    ensures *c == 0 ;
 behavior a_times_b_overflows:
    assumes 0 < a <= SIZE_MAX / 2 ;
    assumes 0 < b <= SIZE_MAX / 2 ;
    assumes (a + b) > (SIZE_MAX / (a < b ? a : b)) ;
    ensures \result == 0 ;
    ensures *c == 0 ;
 behavior a_times_b_computed:
    assumes 0 < a <= SIZE_MAX / 2 ;
    assumes 0 < b <= SIZE_MAX / 2 ;
    assumes (a + b) <= (SIZE_MAX / (a < b ? a : b)) ;
    ensures \result == 1 ;
    ensures *c == (size_t)(a * b) ;
 complete behaviors ;
 disjoint behaviors ;
 */
bool GB_size_t_multiply     // true if ok, false if overflow
(
    size_t *c,              // c = a*b, or zero if overflow occurs
    const size_t a,
    const size_t b
)
{

    ASSERT (c != NULL) ;

    (*c) = 0 ;
    if (a == 0 || b == 0)
    {
        return (true) ;
    }

    if (a > SIZE_MAX / 2 || b > SIZE_MAX / 2)
    {
        // a or b are out of range
        return (false) ;
    }

    // a + b is now safe to compute
    if ((a + b) > (SIZE_MAX / IMIN (a,b)))
    {
        // a * b may overflow
        return (false) ;
    }

    // a * b will not overflow
    (*c) = a * b ;
    return (true) ;
}

