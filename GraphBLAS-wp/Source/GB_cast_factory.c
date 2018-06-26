//------------------------------------------------------------------------------
// GB_cast_factory: return a pointer to a typecasting function
//------------------------------------------------------------------------------

// SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
// http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

// *** JENNA CHANGE 6/25/18 ***
// Changed WORKER macro definition to include the type codes
// Other files need the type codes in WORKER def for the new CAST macro
// Therefore calls to WORKER in GB_2type_template.c require type codes which affects this file
// This one doesn't use the type codes like the others, but needs them for GB_2type_template.c
// WORKER calls

//------------------------------------------------------------------------------

// return a pointer to a function f(z,x,s) that copies its input x into its
// output z, casting as needed.  That is, it computes z = (type of z) x.
// s is the size for user-defined types, which can only be copied.

#include "GB.h"

GB_cast_function GB_cast_factory   // returns pointer to function to cast x to z
(
    const GB_Type_code code1,      // the type of z, the output value
    const GB_Type_code code2       // the type of x, the input value
)
{

    //--------------------------------------------------------------------------
    // check inputs
    //--------------------------------------------------------------------------

    ASSERT (GB_Type_code_compatible (code1, code2)) ;
    ASSERT (code1 <= GB_UDT_code) ;
    ASSERT (code2 <= GB_UDT_code) ;

    //--------------------------------------------------------------------------
    // define the worker for the switch factory
    //--------------------------------------------------------------------------

    // the worker selects a typecast function and returns it to the caller
    #define WORKER(ztype,xtype,zcode,xcode) return (&GB_cast_ ## ztype ## _ ## xtype) ;

    //--------------------------------------------------------------------------
    // launch the switch factory
    //--------------------------------------------------------------------------

    // switch factory for two built-in types; user types are skipped.
    // no generic worker so the switch factory cannot be disabled.
    #include "GB_2type_template.c"
    #undef WORKER

    //--------------------------------------------------------------------------
    // user-defined types fall through the switch factory to here
    //--------------------------------------------------------------------------

    return (&GB_copy_user_user) ;       // if code1 or code2 are GB_UDT_code
}

