//------------------------------------------------------------------------------
// GB_queue_remove: remove a matrix from the matrix queue
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// Modified by Jenna Wise.
// *** JENNA CHANGE 6/23/18 ***
// Commented out the use of openmp #pragmas
// Frama-C does not support openmp #pragmas

// *** JENNA CHANGE 7/28/18 ***
// Commented update to global queue, because not doing verification on matrix queue
// nor global struct

//------------------------------------------------------------------------------

#include "GB.h"
#include "annotlib.h" // for common predicates & logic functions

/*@
 requires A != \null ;
 requires \valid(A) ;
 
 assigns A->queue_prev ;
 assigns A->queue_next ;
 assigns A->enqueued ;
 
 ensures A->queue_prev == \null ;
 ensures A->queue_next == \null ;
 ensures A->enqueued == \false ;
 
 behavior matrix_invalid :
    assumes !matrix_valid(A) ;
    ensures \true ;
 
 behavior matrix_valid :
    assumes matrix_valid(A) ;
    ensures matrix_valid(A) ;
 */
void GB_queue_remove            // remove matrix from queue
(
    GrB_Matrix A                // matrix to remove
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    ASSERT (A != NULL) ;

    //--------------------------------------------------------------------------
    // remove the matrix from the queue, if it is in the queue
    //--------------------------------------------------------------------------

    if (A->enqueued)
    {
        // remove the matrix from the queue
        // #pragma omp critical (GB_queue)
        {
            // check again to be safe, and remove A from the queue
            if (A->enqueued)
            {
               /* GrB_Matrix Prev = (GrB_Matrix) (A->queue_prev) ;
                GrB_Matrix Next = (GrB_Matrix) (A->queue_next) ;
                if (Prev == NULL)
                {
                    // matrix is at the head of the queue; update the head
                    GB_Global.queue_head = Next ;
                }
                else
                {
                    // matrix is not the first in the queue
                    Prev->queue_next = Next ;
                }
                if (Next != NULL)
                {
                    // update the previous link of the next matrix, if any
                    Next->queue_prev = Prev ;
                }*/
                // A has been removed from the queue
                A->queue_prev = NULL ;
                A->queue_next = NULL ;
                A->enqueued = false ;
            }
        }
    }
}

