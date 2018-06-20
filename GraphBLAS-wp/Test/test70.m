function test70
%TEST70 performance comparison of triangle counting methods
%
% This test saves its results in test70_results.mat, so it
% can be restarted.  Results already obtained will be skipped.
% This is useful since MATLAB can crash on some matrices,
% with 'Killed', if it asks for way too much memory.
%
% It would be better to modify this test to check the
% memory usage before trying the matrix multiply.
% See test71.m, which does this:
%
%   % get nnz(C), flops, and memory for C=A*B:
%   s = ssmultsym (A, B) ;
%   % which returns a struct with these 3 statistics, 
%   % without doing any work, and requiring almost no memory
%   % See SuiteSparse/MATLAB_tools/SSMULT

%  SuiteSparse:GraphBLAS, Timothy A. Davis, (c) 2017-2018, All Rights Reserved.
%  http://suitesparse.com   See GraphBLAS/Doc/License.txt for license.

addpath ('../Demo/MATLAB') ;

% get all square matrices and sort by nnz(A)
index = ssget ;
f = find (index.nrows == index.ncols) ;
[~, i] = sort (index.nnz (f)) ;
f = f (i) ;

% f = 936
% f = f (1)
nmat = length (f) ;
figure (1)

% matrices too big for some methods.  0: skip that method
if (ismac || ispc)
    % assume this is a laptop with limited memory
    results = 'test70_results' ;
    skip = [
        %id  methods 0:9
        1294 0 1 1 1 0 1 1 1 1 
        2240 0 1 1 1 0 1 1 1 1
        2229 1 1 1 1 0 1 1 1 1
        1323 0 0 0 1 0 1 1 1 1
        1324 0 0 0 1 0 1 1 1 1
        1320 0 0 0 1 0 1 1 1 1
        1321 0 0 0 1 0 1 1 1 1
        1322 0 0 0 1 0 1 1 1 1
        2234 0 1 1 1 0 1 1 1 1
        1415 0 0 0 1 0 1 1 1 1
        2275 0 0 0 1 0 1 1 1 1
        2136 0 1 1 1 0 1 1 1 1
        2241 0 0 0 1 0 1 1 1 1
        %
        1383 0 0 0 1 0 1 1 1 1
            ] ;
    % when Nedges > limit, do only MATLAB:Sandia,
    % GraphBLAS:Sandia, and GraphBLAS:Sandia2.
    % The others can fail badly
    limit = 1e6 ;
else
    % assume this is a large server
    results = 'test70_results_big' ;
    skip = [
        1383 0 0 0 1 0 1 1 1 1
    ] ;
    limit = 1e6 ;
end

try
    load (results) ; % test70_results
catch
    T = nan (nmat, 9) ;
    Nedges = nan (nmat, 1) ;
    Nnodes = nan (nmat, 1) ;
end

tstart = cputime ;

for k = 1:nmat

    if (~isnan (Nnodes (k)))
        continue ;
    end

    id = f (k) ;
    Prob = ssget (id, index) ;
    A = Prob.A ;
    name = Prob.name ;
    clear Prob

    % remove the diagonal and extract L and U
    A = spones (A) ;
    A = spones (A+A') ;
    L = tril (A,-1) ;
    U = triu (A,1) ;
    A = L + U ;
    n = size (A,1) ;
    nz = nnz (L) ;

    % create the edge incidence matrix
    E = adj_to_edges (A) ;

    fprintf ('\nid %4d Matrix %s\n', id, name) ;
    fprintf ('n %d edges %d\n', n, nz) ;
    ntri = -1 ;
    diary off
    diary on

    Nedges (k) = nz ;
    Nnodes (k) = n ;

    % count the triangles in MATLAB and in GraphBLAS

    method_list = {'minitri', 'Burkhardt', 'Cohen', 'Sandia', 'SandiaL', 'SandiaDot'} ;
    m = 0 ;

    % see what methods to skip
    dothis = find (id == skip (:,1)) ;
    if (~isempty (dothis))
        dothis = skip (dothis, 2:10) ;
    else
        dothis = true (1,9) ;
    end

    for gb = 0:1
        for kk = 1:(5+gb)
            method = method_list {kk} ;
            m = m + 1 ;
            if (nz > limit)
                % do only MATLAB:Sandia, GraphBLAS:Sandia*
                % leave other timings as NaN, not inf
                if (~(m == 4 || m == 10 || m == 11 || m == 12))
                    continue
                end
            end
            nt = -1 ;
            t = inf ;
            if (dothis (m))
                try
                    if (gb)
                        % use GraphBLAS
                        [nt t] = GB_mex_tricount (kk-1, A, E, L, U) ;
                    else
                        % use MATLAB, unless the matrix fails
                        [nt t] = tricount (method, A, E) ;
                    end
                catch
                    % method failed (out of memory)
                end
            end
            % check the result
            if (nt ~= -1)
                if (ntri == -1)
                    ntri = nt ;
                    fprintf ('# triangles: %d\n', ntri) ;
                end
                assert (nt == ntri) ;
            end
            if (gb)
                fprintf ('GraphBLAS: %10s %10.4f\n', method, t) ;
            else
                fprintf ('MATLAB:    %10s %10.4f\n', method, t) ;
            end
            T (k, m) = t ;
        end
    end

    clear A L U E

    % save the results and redraw the plot, but wait at least 5 seconds
    tnow = cputime - tstart ;
    if (tnow > 5)
        save (results, 'T', 'Nedges', 'Nnodes', 'f') ;
        test70_plot (T, Nedges, Nnodes) ;
        tstart = cputime ;
        % also flush the diary
    end

end

