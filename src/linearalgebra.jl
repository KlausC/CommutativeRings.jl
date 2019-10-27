
# linear algebra

struct LU_total{T,MT}
    factors::MT
    pivr::Vector{Int}
    pivc::Vector{Int}
    rank::Int
end

# find maximal element in A[i:end,j]
function pivot(A::Matrix, i::Integer, j::Integer)
    amax = abs(A[i,j])
    imax = i
    m = last(axes(A,1))
    for k = i+1:m
        bmax = abs(A[k,j])
        if bmax > amax
            amax = bmax;
            imax = k
        end
    end
    amax, imax
end

function swaprows(A::Matrix, pr::Vector, i::Integer, j::Integer)
    pr[i], pr[j] = pr[j], pr[i]
    for k = axes(A, 2)
        A[i,k], A[j,k] = A[j,k], A[i,k]
    end
end
function swapcols(A::Matrix, pc::Vector, i::Integer, j::Integer)
    pc[i], pc[j] = pc[j], pc[i]
    for k = axes(A, 1)
        A[k,i], A[k,j] = A[k,j], A[k,i]
    end
end

# L-U factorization of irregular matix A.
# left upper rxr A is regular. right lower corner consits of elements a with abs(a) == 0
# The element type must assure, that isinvertible(a) <=> abs(a) != 0
# 0 <= abs(a) ∈ Real
# Input matrix A is overwritten with the components of L and R.
# Return r = rank(A) and permutation vectors for rows and columns
function lu_total!(A::Matrix{T}) where T
    m, n = size(A)
    mn = min(m, n)
    pr = collect(1:m)
    pc = collect(1:n)
    jmax = mn
    for j = 1:mn
        amax, imax = pivot(A, j, j)
        if !iszero(amax)
            if imax != j
                swaprows(A, pr, j, imax)
            end
        else
            amax = zero(amax)
            imax = 0
            kmax = j
            while kmax < n && iszero(amax)
                kmax += 1
                amax, imax = pivot(A, j, kmax)
            end
            if !iszero(amax)
                swapcols(A, pc, j, kmax)
                if imax != j
                    swaprows(A, pr, j, imax)
                end
            else
                jmax = j - 1
            end
        end
        iszero(amax) && break
        aa = A[j, j]
        for i = j+1:m
            ab = A[i,j] / aa
            A[i,j] = ab
            for k = j+1:n
                A[i,k] -= A[j,k] * ab
            end
        end
    end
    LU_total{T,Matrix{T}}(A, pr, pc, jmax)
end

import LinearAlgebra: UpperTriangular, Diagonal, nullspace, rank
function nullspace(fac::LU_total{T}) where T
    r = rank(fac)
    A = fac.factors
    m = size(A, 2)
    r == 0 && return Diagonal(ones(T, m))
    r == m && return Matrix{T}(undef, m, 0)
    M = [-UpperTriangular(view(A, 1:r, 1:r)) \ view(A, 1:r, r+1:m); Matrix(Diagonal(ones(T, m-r)))]
    pc = fac.pivc
    M[invperm(pc),:]
end

function rank(fac::LU_total) where T
    fac.rank
end

nullspace(A::Matrix) = nullspace(lu_total!(copy(A)))
rank(A::Matrix) = rank(lu_total!(copy(A)))

