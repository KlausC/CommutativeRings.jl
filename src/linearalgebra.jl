
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

# partial L-U factorization of irregular matix A.
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
    jmax = 0
    for j = 1:mn
        amax, imax = pivot(A, j, j)
        if !iszero(amax)
            if imax != j
                swaprows(A, pr, j, imax)
            end
        else
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
            end
        end
        iszero(amax) && break
        jmax = j
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

function lu_total!(A::D) where {T,D<:Diagonal{T}}
    n = size(A, 1)
    pr = collect(1:n)
    pc = copy(pr)
    jmax = 0
    for i = 1:n
        j = i
        while j <= n && iszero(abs(A[j,j]))
            j += 1
        end
        j > n && break
        jmax += 1
        if i != j
            pr[i], pr[j] = pr[j], pr[i]
            A.diag[i], A.diag[j] = A.diag[j], A.diag[i]
        end
    end
    LU_total{T,D}(A, pr, copy(pr), jmax)
end

import LinearAlgebra: Matrix, UpperTriangular, Diagonal, nullspace, rank, size
nullspace(A::Union{LU_total,AbstractMatrix{<:Ring}}) = VectorSpace(nullbase(A))

function nullbase(fac::LU_total{T}) where T
    r = rank(fac)
    A = fac.factors
    m = size(A, 2)
    r == 0 && return Diagonal(ones(T, m))
    r == m && return Matrix{T}(undef, m, 0)
    M = [-UpperTriangular(view(A, 1:r, 1:r)) \ view(A, 1:r, r+1:m); diagm(ones(T, m-r))]
    pc = fac.pivc
    M[invperm(pc),:]
end
nullbase(A::AbstractMatrix{<:Ring}) = nullbase(lu_total!(copy(A)))

function rank(fac::LU_total) where T
    fac.rank
end

rank(A::AbstractMatrix{<:Ring}) = rank(lu_total!(copy(A)))

function VectorSpace(A::AbstractMatrix{<:Ring})
    m = size(A, 1)
    fac = lu_total!(copy(A))
    r = fac.rank
    M = fac.factors
    M = M[r+1:m,1:r] * UnitLowerTriangular(M[1:r,1:r])^-1
    VectorSpace(M, fac.pivr)
end
VectorSpace(A::AbstractVector{<:Ring}) = VectorSpace(hcat(A))

function Matrix(v::VectorSpace)
    vcat(diagm(ones(Int,rank(v))), v.base)[invperm(v.pivr),:]
end

function size(v::VectorSpace)
    s1, s2 = size(v.base)
    (s1 + s2, s2)
end
rank(v::VectorSpace) = size(v, 2)
size(v::VectorSpace, i::Integer) = i == 1 ? sum(size(v.base)) : size(v.base, 2)

import Base: intersect, sum
function intersect(v::V, w::V) where {T,V<:VectorSpace{T}}
    m, r = size(v)
    n, s = size(w)
    s < r && return intersect(w, v)
    m == n || throw(ArgumentError("dimension mismatch of vector spaces ($m,$n)"))
    BT = eltype(T)
    vpiv = v.pivr
    wpiv = invperm(w.pivr)
    AB = vcat(diagm(ones(BT, s)), w.base)[wpiv[vpiv],:]
    LAB = v.base * AB[1:r,:] - AB[r+1:m,:]
    N = nullspace(LAB)
    rr = rank(N)
    N = vcat(diagm(ones(BT,rr)), N.base)[invperm(N.pivr),:]
    VectorSpace(AB[invperm(vpiv),:] * N)
end

function sum(v::V, w::V) where {T,V<:VectorSpace{T}}
    m, r = size(v)
    n, s = size(w)
    s > r && return sum(w, v)
    m == n || throw(ArgumentError("dimension mismatch of vector spaces ($m,$n)"))
    BT = eltype(T)
    vbase = v.base
    vpiv = copy(v.pivr)
    wpiv = invperm(w.pivr)
    AB = vcat(diagm(ones(BT, s)), w.base)[wpiv[vpiv],:]
    LAB = AB[r+1:n,:] - vbase * AB[1:r,:]
    N = VectorSpace(LAB)
    rr = rank(N)
    spiv = N.pivr
    sbase = N.base
    vpiv[r+1:n] = vpiv[spiv .+ r]
    v1 = vbase[spiv[rr+1:n-r],:]
    v2 = sbase * vbase[spiv[1:rr],:]
    VectorSpace(hcat(v1 - v2, sbase), vpiv)
end

function complement(v::VectorSpace{T}) where T
    m, r = size(v)
    piv = vcat(v.pivr[r+1:m], v.pivr[1:r])
    base = reshape(zero(v.base), r, m-r)
    VectorSpace(base, piv)
end

import Base: ==, issubset
==(v::V, w::V) where V<:VectorSpace = size(v) == size(w) && rank(v) == rank(intersect(v, w)) 
issubset(v::V, w::V) where V<:VectorSpace = size(v, 1) == size(w, 1) && rank(w) >= rank(v) == rank(intersect(v, w)) 

