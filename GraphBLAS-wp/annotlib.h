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
 predicate magic_valid(int64_t magic) = magic == 0x00981B0787374E72 ;
 */

//------------------------------------------------------------------------------
// GrB_Type
//------------------------------------------------------------------------------

// no footprint
/*@
 logic int type_code{L}(GrB_Type t) = t->code ;
 
 logic size_t type_size{L}(GrB_Type t) = t->size ;
 
 predicate type_init{L}(GrB_Type t) = magic_valid(t->magic) ;
 
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
           ((char*)o->function) + (0..sizeof(o->function)-1),
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
               ((char*)o->function) + (0..sizeof(o->function)-1),
               o->ztype) &&
    \separated(o,
               ((char*)o->function) + (0..sizeof(o->function)-1),
               o->xtype) &&
    \separated(o,
               ((char*)o->function) + (0..sizeof(o->function)-1),
               o->ytype) ;
 */

/*@
 predicate binaryop_valid{L}(GrB_BinaryOp o) =
    \valid(o) &&
    binaryop_init(o) &&
    \valid(((char*)binaryop_func(o)) + (0..sizeof(binaryop_func(o))-1)) &&
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
         \valid(((char*)(m->xpending + (0..(m->max_npending)-1))) +
            (0..type_size(matrix_type(m))-1))
         &&
         tuple_indices_in_bounds :
            (\forall int64_t k; 0 <= k < m->npending ==>
                (0 <= (m->ipending)[k] < matrix_nrows(m)) &&
                (0 <= (matrix_ncols(m) <= 1 ? 0 : ((m->jpending)[k])) < matrix_ncols(m))
            )
         &&
         tuple_indices_sorted :
            (m->sorted_pending == \true ?
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
 
 // check p, i, x, pix pendings, and zombies
 predicate matrix_storage_valid{L}(GrB_Matrix m) =
    \valid(m->p + (0..(matrix_ncols(m)+1)-1))
    &&
    (matrix_nvals(m) == 0 ?
        (m->x != \null || m->i != \null || m->i_shallow || m->x_shallow ?
            \false :
            (col_ptrs_valid :
                \forall int64_t j; 0 <= j < matrix_ncols(m) ==> (m->p)[j] == 0
            )
        ) :
        (m->x == \null || m->i == \null ?
            \false :
            ((m->p)[0] != 0 ? \false : \true)
            &&
            col_ptrs_valid :
                (\forall int64_t j; 0 <= j < matrix_ncols(m) ==>
                    (m->p)[j] <= (m->p)[j+1] <= matrix_nvals(m)
                )
            &&
            \valid(((char*)(m->x + (0..(matrix_nvals(m))-1))) +
                (0..type_size(matrix_type(m))-1))
            &&
            row_indices_valid(m)
        )
    )
    &&
    0 <= m->nzombies <= (m->p)[matrix_ncols(m)]
    &&
    pending_tuples_valid(m) ;
 
 predicate matrix_fp_separated{L}(GrB_Matrix m) =
    \separated(m,
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
 */

/*@
 // nrows, ncols should be >0 by spec, but implementation check says >=0
 predicate matrix_valid{L}(GrB_Matrix m) =
    \valid(m) &&
    matrix_init(m) &&
    0 < matrix_nrows(m) <= ((GrB_Index)(1ULL << 60)) &&
    0 < matrix_ncols(m) <= ((GrB_Index)(1ULL << 60)) &&
    0 <= matrix_nvals(m) <= ((GrB_Index)(1ULL << 60)) &&
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
