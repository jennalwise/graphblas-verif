//------------------------------------------------------------------------------
// GB_qsort_template: sort an n-by-K list of integers
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

//------------------------------------------------------------------------------

// This file is #include'd in GB_qsort*.c to create specific versions for K =
// 1, 2, and 3.  Requires an inline or macro definition of the lt function.
// The lt function has the form lt (A,i,B,j) and returns true if A[i]<B[j].

// All of these functions are static; there will be versions of them in each
// variant of GB_qsort*, with the same names.  They are called only by the
// GB_qsort* function in the #include'ing file.

//------------------------------------------------------------------------------
// partition: use a pivot to partition an array
//------------------------------------------------------------------------------

// C.A.R Hoare partition method, partitions an array in place via a pivot.
// k = partition (A, n) partitions A [0:n-1] such that all entries in
// A [0:k] are <= all entries in A [k+1:n-1].

static inline int64_t partition
(
    args (int64_t, A),
    const int64_t n
)
{

    // select a pivot at random
    int64_t pivot = ((n < GB_RAND_MAX) ? GB_rand15 ( ) : GB_rand ( )) % n ;

    // get the pivot entry
    int64_t Pivot_0 [1] ; Pivot_0 [0] = A_0 [pivot] ;
    #if K > 1
    int64_t Pivot_1 [1] ; Pivot_1 [0] = A_1 [pivot] ;
    #endif
    #if K > 2
    int64_t Pivot_2 [1] ; Pivot_2 [0] = A_2 [pivot] ;
    #endif

    // At the top of the while loop, A [left+1...right-1] is considered, and
    // entries outside this range are in their proper place and not touched.
    // Since the input specification of this function is to partition A
    // [0..n-1], left must start at -1 and right must start at n.
    int64_t left = -1 ;
    int64_t right = n ;

    // keep partitioning until the left and right sides meet
    while (true)
    {
        // loop invariant:  A [0..left] < pivot and A [right..n-1] > pivot,
        // so the region to be considered is A [left+1 ... right-1].

        // increment left until finding an entry A [left] >= pivot
        do { left++ ; } while (lt (A, left, Pivot, 0)) ;

        // decrement right until finding an entry A [right] <= pivot
        do { right-- ; } while (lt (Pivot, 0, A, right)) ;

        // now A [0..left-1] < pivot and A [right+1..n-1] > pivot, but
        // A [left] > pivot and A [right] < pivot, so these two entries
        // are out of place and must be swapped.

        // However, if the two sides have met, the partition is finished.
        if (left >= right)
        {
            // A has been partitioned into A [0:right] and A [right+1:n-1].
            // k = right+1, so A is split into A [0:k-1] and A [k:n-1].
            return (right + 1) ;
        }

        // since A [left] > pivot and A [right] < pivot, swap them
        swap (A, left, right) ;

        // after the swap this condition holds:
        // A [0..left] < pivot and A [right..n-1] > pivot
    }
}

//------------------------------------------------------------------------------
// quicksort
//------------------------------------------------------------------------------

static void quicksort       // sort A [0:n-1]
(
    args (int64_t, A),      // array(s) to sort
    const int64_t n         // size of A
)
{

    if (n < 20)
    {
        // in-place insertion sort on A [0:n-1], where n is small
        for (int64_t k = 1 ; k < n ; k++)
        {
            for (int64_t j = k ; j > 0 && lt (A, j, A, j-1) ; j--)
            {
                // swap A [j-1] and A [j]
                swap (A, j-1, j) ;
            }
        }
    }
    else
    {
        // partition A [0:n-1] into A [0:k-1] and A [k:n-1]
        int64_t k = partition (arg (A), n) ;

        // sort each partition
        quicksort (arg (A), k) ;                // sort A [0:k-1]
        quicksort (arg_offset (A, k), n-k) ;    // sort A [k+1:n-1]
    }
}

