//------------------------------------------------------------------------------
// GB_free_memory: wrapper for free
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// Modified by Jenna Wise.
// *** JENNA CHANGE 6/22/18 ***
// Commented out the use of openmp #pragmas
// Frama-C does not support openmp #pragmas
// Commented out update of global malloc tracking to simplify verification annotations

// *** JENNA ANNOTATION 7/28/18 ***
// GB_free_memory

//------------------------------------------------------------------------------

// A wrapper for FREE.  If p is NULL on input, it is not freed.

// By default, FREE is defined in GB.h as free.  For a MATLAB mexFunction, it
// is mxFree.  It can also be defined at compile time with -DFREE=myfreefunc.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 frees p ;
 assigns __fc_heap_status ;
 behavior p_null :
    assumes p == \null ;
    ensures p == \null ;
 behavior p_not_null :
    assumes p != \null ;
    requires \freeable(p) ;
    ensures \allocable(p) ;
 complete behaviors ;
 disjoint behaviors ;
 */
void GB_free_memory
(
    void *p,                // pointer to allocated block of memory to free
    size_t nitems,          // number of items to free
    size_t size_of_item     // sizeof each item
)
{
    if (p != NULL)
    {
        // at least one item is always allocated
 /*       nitems = IMAX (1, nitems) ;
        int nmalloc ;

        // #pragma omp critical (GB_memory)
        {
            nmalloc = --GB_Global.nmalloc ;
            GB_Global.inuse -= nitems * size_of_item ;
        }

#ifdef PRINT_MALLOC
        printf ("free:    %14p %3d %1d n "GBd" size "GBd"\n", 
            p, nmalloc, GB_Global.malloc_debug,
            (int64_t) nitems, (int64_t) size_of_item) ;
        if (nmalloc < 0)
        {
            printf ("%d free    %p negative mallocs!\n", nmalloc, p) ;
        }
#endif
*/
        FREE (p) ;
 //       ASSERT (nmalloc >= 0) ;
    }
}

