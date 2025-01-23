
# linear algebra

struct LU_total{T,MT}
    factors::MT
    pivr::Vector{Int}
    pivc::Vector{Int}
    rank::Int
end

"""
    pivot(A, i, j)

Find maximal element in `A[i:end,j]`
"""
function pivot(A::Union{AbstractMatrix,AbstractVector}, i::Integer, j::Integer = 1)
    m = size(A, 1)
    amax = pivabs(A[i+(j-1)*m])
    imax = i
    for k = i+1:m
        bmax = pivabs(A[k+(j-1)*m])
        if bmax > amax
            amax = bmax
            imax = k
        end
    end
    amax, imax
end

pivabs(a::QQ) = pivabs(ZZ(numerator(a)))
pivabs(z::ZZ) = iszero(z) ? 0.0 : isunit(z) ? Inf : 1.0 / abs(z.val)
pivabs(a::Ring) = isunit(a) ? 1 : 0

"""
    swaprows(A, pr, i, j, cols)

Swap rows `A[i,cols]` with `A[j,cols]` and `pr[i]` with `pr[j]`
"""
function swaprows(
    A::Matrix{T},
    pr::Vector,
    i::Integer,
    j::Integer,
    cols = axes(A, 2),
) where T
    pr[i], pr[j] = pr[j], pr[i]
    for k in cols
        A[i, k], A[j, k] = A[j, k], A[i, k]
    end
end
"""
    swapcols(A, pc, i, j)

Swap columns `A[:,i]` with `A[:,j]` and `pc[i]` with `pc[j]`
"""
function swapcols(A::Matrix{T}, pc::Vector, i::Integer, j::Integer) where T
    pc[i], pc[j] = pc[j], pc[i]
    for k in axes(A, 1)
        A[k, i], A[k, j] = A[k, j], A[k, i]
    end
end

"""
    lu_total!(A::AbstractMatrix)

Compute partial L-U factorization of general matrix A.

Left upper rxr A is regular. right lower corner consits of elements a with abs(a) == 0
The element type must assure, that isunit(a) <=> abs(a) != 0
`0 <= abs(a) ∈ Real`
Input matrix A is overwritten with the components of L and U.
Return r = rank(A) and permutation vectors for rows and columns
"""
function lu_total!(A::AbstractMatrix{T}) where T
    lu_total!(A, category_trait(T))
end
function lu_total!(A::AbstractMatrix{T}, ::Type{<:FieldTrait}) where T
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
            ab = A[i, j] / aa
            A[i, j] = ab
            for k = j+1:n
                A[i, k] -= A[j, k] * ab
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
        while j <= n && iszero(pivabs(A[j, j]))
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

# assuming A[:,1:k-1] contain partial L-U decomposition of A[pr,:]
# add b as additional column.
function lu_incremental!(
    A::Matrix{T},
    pr::Vector{<:Integer},
    k::Integer,
    b::AbstractVector{T},
) where T
    m, n = size(A)
    if length(b) != m
        throw(ArgumentError("vector length must be equal to first dimension of matrix"))
    end
    if n < k
        throw(ArgumentError("number of columns of matrix not sufficient"))
    end
    permute!(b, pr)
    for j = 2:m
        s = b[j]
        for i = 1:min(j - 1, k - 1)
            s -= A[j, i] * b[i]
        end
        b[j] = s
    end
    if k <= m
        amax, imax = pivot(b, k)
        if !iszero(amax)
            if imax != k
                swaprows(A, pr, k, imax, 1:k-1)
                b[k], b[imax] = b[imax], b[k]
            end
            aa = inv(b[k])
            for j = k+1:m
                b[j] *= aa
            end
        end
    end
    A
end

function lu_rowpivot!(A::Matrix{T}) where T
    m, n = size(A)
    pr = collect(1:m)
    pc = collect(1:n)
    rank = 0
    for j = 1:n
        lu_incremental!(A, pr, j, view(A, :, j))
        if j <= m
            if !iszero(A[j, j])
                rank = j
            else
                break
            end
        end
    end
    LU_total{T,Matrix{T}}(A, pr, pc, rank)
end

"""
    lu_axu(A, u)

Calculate partial lu-factorization of `[u A*u A^2*u A^(rank-1)*u]` with row pivoting.
Return `LU_total` factorization where `L` and `R` are extended by unit base.
As second output return `A^rank*u`.
"""
function lu_axu(A::AbstractMatrix{R}, u::AbstractVector{R}) where R
    n = checksquare(A)
    n == length(u) || throw(ArgumentError("vector dimension must match matrix"))
    pr = collect(1:n)
    B = zeros(R, n, n)
    rank = 0
    for j = 1:n
        v = copy(u)
        lu_incremental!(B, pr, j, v)
        iszero(v[j]) && break
        rank = j
        B[:, j] .= v
        u = A * u
    end
    for j = rank+1:n
        B[pr[j], j] = one(R)
    end
    pc = collect(1:n)
    LU_total{R,Matrix{R}}(B, pr, pc, rank), u
end

function Base.propertynames(::LU_total)
    tuple(fieldnames(LU_total)..., :L11, :U11, :L_1, :L21, :L, :U)
end
function Base.getproperty(lut::LU_total, s::Symbol)
    r = getfield(lut, :rank)
    factors = getfield(lut, :factors)
    m, n = size(factors)
    if s === :L11
        UnitLowerTriangular(view(factors, 1:r, 1:r))
    elseif s === :L_1
        [lut.L11; lut.L21]
    elseif s === :L
        [lut.L_1 [zeros(Int, r, m - r); I(m - r)]]
    elseif s === :L21
        view(factors, r+1:m, 1:r)
    elseif s === :U11
        UpperTriangular(view(factors, 1:r, 1:r))
    elseif s === :U
        [lut.U11 zeros(Int, r, n - r); zeros(Int, m - r, r) I(n - r)]
    else
        getfield(lut, s)
    end
end

import LinearAlgebra: Matrix, UpperTriangular, Diagonal, nullspace, rank, size
nullspace(A::Union{LU_total,AbstractMatrix{<:Ring}}) = VectorSpace(nullbase(A))

function nullbase(fac::LU_total{T}) where T
    r = rank(fac)
    A = fac.factors
    m = size(A, 2)
    r == 0 && return Diagonal(ones(T, m))
    r == m && return Matrix{T}(undef, m, 0)
    M = [-UpperTriangular(view(A, 1:r, 1:r)) \ view(A, 1:r, r+1:m); diagm(ones(T, m - r))]
    pc = fac.pivc
    M[invperm(pc), :]
end
nullbase(A::AbstractMatrix{<:Ring}) = nullbase(lu_total!(copy(A)))

function LinearAlgebra.rank(fac::LU_total)
    fac.rank
end

LinearAlgebra.rank(A::AbstractMatrix{<:Ring}) = rank(lu_total!(copy(A)))

"""
    VectorSpace(v::AbstractVector...)

Vector space generated by the vectors or matrix.
To obtain a basis of the space, use `Matrix(::VectorSpace)`.
"""
function VectorSpace(A1::AbstractArray{R}, A::AbstractArray{R}...) where {R<:Ring}
    B = convert(Array, hcat(A1, A...))
    m = size(B, 1)
    fac = lu_total!(B)
    r = fac.rank
    M = fac.factors
    M = M[r+1:m, 1:r] * UnitLowerTriangular(M[1:r, 1:r])^-1
    VectorSpace{R}(M, fac.pivr)
end

function Matrix(v::VectorSpace)
    vcat(diagm(ones(Int, rank(v))), v.base)[invperm(v.pivr), :]
end

function size(v::VectorSpace)
    s1, s2 = size(v.base)
    (s1 + s2, s2)
end
rank(v::VectorSpace) = size(v, 2)
size(v::VectorSpace, i::Integer) = i == 1 ? sum(size(v.base)) : size(v.base, 2)

import Base: intersect, sum
"""
    intersect(v1::V, v2::V)::V where V<:VectorSpace

Intersection of two vector spaces.
"""
function intersect(v::V, w::V) where {T,V<:VectorSpace{T}}
    m, rv = size(v)
    n, rw = size(w)
    rv <= rw || return intersect(w, v)
    m == n || throw(ArgumentError("dimension mismatch of vector spaces ($m,$n)"))
    if rv == 0 || rw == m
        return v
    end
    BT = T
    vpiv = v.pivr
    wpiv = invperm(w.pivr)
    AB = vcat(diagm(ones(BT, rw)), w.base)[wpiv[vpiv], :]
    LAB = v.base * AB[1:rv, :] - AB[rv+1:m, :]
    N = nullspace(LAB)
    rr = rank(N)
    N = vcat(diagm(ones(BT, rr)), N.base)[invperm(N.pivr), :]
    VectorSpace(AB[invperm(vpiv), :] * N)
end

"""
    sum(v1::V, v2::V)::V where V<:VectorSpace

Sum of two vector spaces resulting in vector space of same kind.
"""
function Base.sum(v::V, w::V) where {T,V<:VectorSpace{T}}
    m, rv = size(v)
    n, rw = size(w)
    rv >= rw || return sum(w, v)
    m == n || throw(ArgumentError("dimension mismatch of vector spaces ($m,$n)"))
    if rw == 0 || rv == m
        return v
    end
    BT = T
    vbase = v.base
    vpiv = copy(v.pivr)
    wpiv = invperm(w.pivr)
    AB = vcat(diagm(ones(BT, rw)), w.base)[wpiv[vpiv], :]
    LAB = AB[rv+1:n, :] - vbase * AB[1:rv, :]
    N = VectorSpace(LAB)
    rr = rank(N)
    spiv = N.pivr
    sbase = N.base
    vpiv[rv+1:n] = vpiv[spiv.+rv]
    v1 = vbase[spiv[rr+1:n-rv], :]
    v2 = sbase * vbase[spiv[1:rr], :]
    VectorSpace{T}(hcat(v1 - v2, sbase), vpiv)
end

"""
    complement(v::V)::V where V<:VectorSpace

Return a complementary space of vector space.
"""
function complement(v::VectorSpace{T}) where T
    m, r = size(v)
    piv = vcat(v.pivr[r+1:m], v.pivr[1:r])
    base = reshape(zero(v.base), r, m - r)
    VectorSpace{T}(base, piv)
end

import Base: ==, issubset, -, +, *
==(v::V, w::V) where V<:VectorSpace = size(v) == size(w) && rank(v) == rank(intersect(v, w))
issubset(v::V, w::V) where V<:VectorSpace =
    size(v, 1) == size(w, 1) && rank(w) >= rank(v) == rank(intersect(v, w))

+(v::V, w::V) where V<:VectorSpace = sum(v, w)
-(v::VectorSpace) = complement(v)
-(v::V, w::V) where V<:VectorSpace = intersect(v, -w)

*(A::AbstractMatrix, v::VectorSpace) = VectorSpace(A * Matrix(v))

*(r::Ring, A::AbstractMatrix) = r .* A
*(A::AbstractMatrix, r::Ring) = A .* r

function +(x::P, A::AbstractMatrix{<:Ring}) where P<:Ring
    n = checksquare(A)
    I(n) .* x + A
end
function +(A::AbstractMatrix{<:Ring}, x::Ring)
    n = checksquare(A)
    A .+ I(n) .* x
end
function -(x::P, A::AbstractMatrix{<:Ring}) where P<:Ring
    n = checksquare(A)
    I(n) .* x - A
end
function -(A::AbstractMatrix{<:Ring}, x::P) where P<:Ring
    n = checksquare(A)
    A - I(n) .* x
end

"""
    characteristic_polynomial(A[, P])

Characteristic polynomial of matrix `A`. `P` is an optional
univariate polynomial type, defaulting to `eltype(A)[:x]`
"""
function characteristic_polynomial(A::AbstractMatrix, T = eltype(A))
    x = monom(T[:x])
    det(x - A)
end

"""
    adjugate(A::AbstractMatrix{<:Ring})

The adjugate of matrix `A`. Invariant is `adjugate(A) * A == det(A) * I`.
"""
function adjugate(A::AbstractMatrix{P}) where P<:Ring
    da = det(A)
    if isunit(da)
        _adjugate(A, da)
    else
        _adjugate_fallback(A)
    end
end
function _adjugate(A::AbstractMatrix{P}, da) where P<:Union{Polynomial,ZZ}
    Q = Frac(P)
    B = Q.(A)
    C = inv(B) .* Q(da)
    numerator.(C)
end
function _adjugate(A::AbstractMatrix{P}, da) where P
    inv(A) * da
end
function _adjugate_fallback(A::AbstractMatrix{P}) where P
    PP = P[:λ]
    Q = Frac(PP)
    B = Q(monom(PP)) + Q.(A)
    d = det(B)
    C = inv(B) .* d
    D = numerator.(C)
    convert.(P, evaluate.(D, 0))
end

"""
    companion(p::UnivariatePolynomial)

Return the companion matrix of monic polynomial `p`.
The negative of `p`'s trailing coefficients are in the last column of the matrix.
Its characteristic polynomial is identical to `p`.
"""
function companion(p::UnivariatePolynomial{T}) where T
    ismonic(p) || throw(ArgumentError("polynomial is not monic"))
    n = deg(p)
    A = diagm(-1 => ones(T, n - 1))
    b = p.first
    for i in 1:length(p.coeff)-1
        A[i+b, n] = -p.coeff[i]
    end
    A
end
