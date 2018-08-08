//------------------------------------------------------------------------------
// GB_Work_free: free the Work workspace array
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA ANNOTATION 8/8/18 ***
// GB_Work_free

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires GB_thread_local.Work == \null || \freeable(GB_thread_local.Work) ;
 
 assigns __fc_heap_status ;
 assigns GB_thread_local.Work_size ;
 assigns GB_thread_local.Work ;
 
 ensures GB_thread_local.Work_size == 0 ;
 ensures GB_thread_local.Work == \null ;
 
 behavior work_null :
    assumes GB_thread_local.Work == \null ;
    frees \nothing ;
    ensures \true ;
 
 behavior work_not_null :
    assumes GB_thread_local.Work != \null ;
    frees GB_thread_local.Work ;
    ensures \allocable(GB_thread_local.Work) ;
 
 complete behaviors ;
 disjoint behaviors ;
 */
void GB_Work_free ( )               // free the Work array
{
    int64_t currsize = GB_thread_local.Work_size ;
    GB_FREE_MEMORY (GB_thread_local.Work, currsize, sizeof (char)) ;
    GB_thread_local.Work_size = 0 ;
}

