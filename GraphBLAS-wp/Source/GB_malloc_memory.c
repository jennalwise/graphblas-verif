//------------------------------------------------------------------------------
// GB_malloc_memory: wrapper for malloc
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// Modified by Jenna Wise.
// *** JENNA CHANGE 6/23/18 ***
// Commented out the use of openmp #pragmas
// Frama-C does not support openmp #pragmas

// *** JENNA CHANGE 7/29/18 ***
// Commented out update of GB_Global struct and malloc checking for it
// Not verifying GB_Global struct

// *** JENNA ANNOTATION 7/29/18 ***
// GB_malloc_memory

//------------------------------------------------------------------------------

// A wrapper for MALLOC.  Space is not initialized.

// Parameters are the same as the POSIX malloc, except that asking to allocate
// a block of zero size causes a block of size 1 to be allocated instead.  This
// allows the return pointer p to be checked for the out-of-memory condition,
// even when allocating an object of size zero.

// By default, MALLOC is defined in GB.h as malloc.  For a MATLAB mexFunction,
// it is mxMalloc.  It can also be defined at compile time with
// -DMALLOC=mymallocfunc.

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 allocates \result ;
 assigns __fc_heap_status ;
 assigns \result ;
 
 behavior inputs_invalid:
    assumes plus_mult_overflow(max((size_t)1,nitems),max((size_t)1,size_of_item)) ||
            max((size_t)1,nitems) > ((GrB_Index)(1ULL << 60))      ||
            max((size_t)1,size_of_item) > ((GrB_Index)(1ULL << 60)) ;
    ensures \result == \null ;
 
 behavior inputs_valid:
    assumes !plus_mult_overflow(max((size_t)1,nitems),max((size_t)1,size_of_item)) ;
    assumes max((size_t)1,nitems) <= ((GrB_Index)(1ULL << 60)) ;
    assumes max((size_t)1,size_of_item) <= ((GrB_Index)(1ULL << 60)) ;
    ensures (\result == \null || \result != \null) ;
    ensures (\result != \null ==>
                \fresh(\result,max((size_t)1,nitems) * max((size_t)1,size_of_item))) ;
    ensures (\result != \null ==>
                \valid(((char*)\result) + (0..max((size_t)1,nitems)*max((size_t)1,size_of_item)-1))) ; // fresh not supported by WP or EVA, so need this redundant stmt for rte
 
 complete behaviors ;
 disjoint behaviors ;
 */
void *GB_malloc_memory      // pointer to allocated block of memory
(
    size_t nitems,          // number of items to allocate
    size_t size_of_item     // sizeof each item
)
{

    void *p ;
    size_t size ;
    int nmalloc ;

    // make sure at least one item is allocated
    nitems = IMAX (1, nitems) ;

    // make sure at least one byte is allocated
    size_of_item = IMAX (1, size_of_item) ;

    bool ok = GB_size_t_multiply (&size, nitems, size_of_item) ;
    if (!ok || nitems > GB_INDEX_MAX || size_of_item > GB_INDEX_MAX)
    {
        // overflow
        p = NULL ;
    }
    else
    {

        // check the malloc debug status.  This debug flag is set outside
        // of GraphBLAS and not modified, so it is safe to check it outside
        // a critical section.
        /*bool pretend_to_fail = false ;
        if (GB_Global.malloc_debug)
        {
            // brutal malloc debug; pretend to fail if the count <= 0
            // #pragma omp critical (GB_memory)
            {
                pretend_to_fail = (GB_Global.malloc_debug_count-- <= 0) ;
            }
        }

        if (pretend_to_fail)
        {
            p = NULL ;
        }
        else
        {*/
            p = (void *) MALLOC (size) ;
        /*}

        if (p != NULL)
        {

            // #pragma omp critical (GB_memory)
            {
                nmalloc = ++GB_Global.nmalloc ;
                GB_Global.inuse += nitems * size_of_item ;
                GB_Global.maxused = IMAX (GB_Global.maxused, GB_Global.inuse) ;
            }

#ifdef PRINT_MALLOC
            printf ("malloc:  %14p %3d %1d n "GBd" size "GBd"\n", 
                p, nmalloc, GB_Global.malloc_debug,
                (int64_t) nitems, (int64_t) size_of_item) ;
#endif
        }*/
    }
    return (p) ;
}

