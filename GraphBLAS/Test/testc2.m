function testc2
%TESTC2 test complex A*B, A'*B, A*B', A'*B', A+B

% SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
% http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

maxerr = 0 ;
for m = [1 5 10 100]
    for n = [1 5 10 100]
        for k = [1 5 10 100]
            A = GB_mex_random (k, m, m*5, 1, 1) ;
            B = GB_mex_random (k, n, n*5, 1, 2) ;
            C = GB_mex_AdotB (A, B) ;
            C2 = A'*B  ;
            err = norm (C-C2,1) ;
            maxerr = max (maxerr, err) ;
            assert (err < 1e-12)
        end
    end
end
fprintf ('All complex A''*B tests passed, maxerr %g\n', maxerr) ;

maxerr = 0 ;
for m = [1 5 10 100]
    for n = [1 5 10 100]
            A = GB_mex_random (m, n, m*5, 1, 1) ;
            B = GB_mex_random (m, n, n*5, 1, 2) ;
            C = GB_mex_AplusB (A, B, 'plus') ;
            C2 = A + B  ;
            err = norm (C-C2,1) ;
            maxerr = max (maxerr, err) ;
            assert (err < 1e-12)
    end
end
fprintf ('All complex A+B tests passed, maxerr %g\n', maxerr) ;

maxerr = 0 ;
for m = [1 5 10 100]
    for n = [1 5 10 100]
        for k = [1 5 10 100]
            for at = 0:1
                for bt = 0:1
                    if (at)
                        A = GB_mex_random (k, m, m*5, 1, 1) ;
                    else
                        A = GB_mex_random (m, k, m*5, 1, 1) ;
                    end
                    if (bt)
                        B = GB_mex_random (n, k, m*5, 1, 1) ;
                    else
                        B = GB_mex_random (k, n, m*5, 1, 1) ;
                    end
                    C = GB_mex_AxB (A, B, at, bt) ;
                    if (at)
                        if (bt)
                            C2 = A'*B'  ;
                        else
                            C2 = A'*B  ;
                        end
                    else
                        if (bt)
                            C2 = A*B'  ;
                        else
                            C2 = A*B  ;
                        end
                    end
                    err = norm (C-C2,1) ;
                    maxerr = max (maxerr, err) ;
                    assert (err < 1e-12)
                end
            end
        end
    end
end

fprintf ('testc2: all complex A*B, A''*B, A*B'', A''*B'' tests passed, maxerr %g\n', maxerr) ;

