//------------------------------------------------------------------------------
// GB_Work_alloc: ensure Work workspace is large enough
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/8/18 ***
// GB_Work_alloc

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 frees GB_thread_local.Work ;
 allocates GB_thread_local.Work ;
 assigns __fc_heap_status ;
 assigns GB_thread_local.Work ;
 assigns GB_thread_local.Work_size ;
 
 behavior inputs_invalid :
    assumes plus_mult_overflow(Work_nitems_required,Work_itemsize) ;
    ensures \result == \false ;
 
 behavior inputs_valid_no_malloc :
    assumes !plus_mult_overflow(Work_nitems_required,Work_itemsize) ;
    assumes (size_t)(Work_nitems_required * Work_itemsize) <= GB_thread_local.Work_size ;
 
    requires (GB_thread_local.Work_size > 0 ==>
                \freeable(GB_thread_local.Work)) ;
    requires (GB_thread_local.Work_size > 0 ==>
                \valid(((char*)GB_thread_local.Work) + (0..GB_thread_local.Work_size-1)) &&
                \block_length(GB_thread_local.Work) == GB_thread_local.Work_size) ;
 
    ensures \result == \true ;
 
 behavior inputs_valid_malloc :
    assumes !plus_mult_overflow(Work_nitems_required,Work_itemsize) ;
    assumes (size_t)(Work_nitems_required * Work_itemsize) > GB_thread_local.Work_size ;
 
    requires (GB_thread_local.Work == \null || \freeable(GB_thread_local.Work)) ;
 
    ensures (\result == \true || \result == \false) ;
    ensures (\result == \false ==>
                GB_thread_local.Work == \null &&
                GB_thread_local.Work_size == 0 &&
                \allocable(GB_thread_local.Work)) ;
    ensures (\result == \true ==>
                GB_thread_local.Work != \null &&
                \fresh(GB_thread_local.Work,
                       ((Work_nitems_required * Work_itemsize)+1)*sizeof(char)) &&
                GB_thread_local.Work_size == (size_t)((size_t)(Work_nitems_required * Work_itemsize)+1)) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
bool GB_Work_alloc                  // allocate Work space
(
    size_t Work_nitems_required,    // ensure Work is at least this large,
    size_t Work_itemsize            // # items times size of each item
)
{

    size_t Work_required ;

    // Work_required = Work_nitems_required * Work_itemsize
    if (!GB_size_t_multiply (&Work_required, 
        Work_nitems_required, Work_itemsize))
    {
        // size_t overflow
        return (false) ;
    }

    if (Work_required > GB_thread_local.Work_size)
    {
        // free the existing space
        GB_Work_free ( ) ;

        // malloc the new space
        size_t newsize = Work_required + 1 ;
        GB_MALLOC_MEMORY (GB_thread_local.Work, newsize, sizeof (char)) ;
        if (GB_thread_local.Work == NULL)
        {
            // out of memory
            return (false) ;
        }
        GB_thread_local.Work_size = newsize ;
    }

    // success
    return (true) ;
}

