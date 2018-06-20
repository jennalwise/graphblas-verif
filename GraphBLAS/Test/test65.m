function test65
%TEST65 test type casting

% SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
% http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

X = logical (rand (4) > 0.5) ;
C = GB_mex_cast (X, 'logical') ;
assert (isequal (X,C)) ;

A = 100 * randn (4) ;

X = int8 (A) ;
C = GB_mex_cast (X, 'int8') ;
assert (isequal (X,C)) ;

X = uint8 (A) ;
C = GB_mex_cast (X, 'uint8') ;
assert (isequal (X,C)) ;

X = int16 (A) ;
C = GB_mex_cast (X, 'int16') ;
assert (isequal (X,C)) ;

X = uint16 (A) ;
C = GB_mex_cast (X, 'uint16') ;
assert (isequal (X,C)) ;

X = int32 (A) ;
C = GB_mex_cast (X, 'int32') ;
assert (isequal (X,C)) ;

X = uint32 (A) ;
C = GB_mex_cast (X, 'uint32') ;
assert (isequal (X,C)) ;

X = int32 (A) ;
C = GB_mex_cast (X, 'int32') ;
assert (isequal (X,C)) ;

X = uint32 (A) ;
C = GB_mex_cast (X, 'uint32') ;
assert (isequal (X,C)) ;

X = single (A) ;
C = GB_mex_cast (X, 'single') ;
assert (isequal (X,C)) ;

X = double (A) ;
C = GB_mex_cast (X, 'double') ;
assert (isequal (X,C)) ;

fprintf ('\ntest65: all tests passed\n') ;

