"""
    rational_normal_form(A::AbstractMatrix{field})

Calculate the rational canonical form factorization of square matrix `A`.
Element type of `A` must be a field.
The form is also known as 'Frobenius normal' form or 'rational canonical form'.

# @see:
The algorithm is derived from the lecture notes
'Klaus Bongartz, Normalformen von Matrizen'
https://www2.math.uni-wuppertal.de/~bongartz/Normalformen.pdf
"""
function rational_normal_form(A::AbstractMatrix{<:Ring})
    rational_normal_form(A, category_trait(eltype(A)))
end
function rational_normal_form(A::AbstractMatrix, ::Type{<:FieldTrait})
    _rational_normal_form(A)
end

"""
    minimal_polynomial(A::AbstractMatrix{F}, u::AbstractVector{F}) where F<:Ring (field)

Calculate the local minimal polynomial ``m_A,u`` of a square matrix `A` over a ring
for vector `u`.

``m_A,u`` is the minimum degree monic polynomial with ``m_A,u(A)*u == 0``
"""
function minimal_polynomial(A::AbstractMatrix{R}, u::AbstractVector{R}) where R<:Ring
    n = checksquare(A)
    n == length(u) || throw(ArgumentError("size of vector does not match matrix"))
    lut, v = lu_axu(A, u)
    r = lut.rank
    U = UpperTriangular(view(lut.factors, 1:r, 1:r))
    L = UnitLowerTriangular(view(lut.factors, 1:r, 1:r))
    w = U \ (L \ v[lut.pivr[1:r]])
    UnivariatePolynomial{R,:x}([-w; 1])
end

"""
    axspace(A, u, n)

Return new matrix `[u A*u A^2*u ... A^(n-1)*u]`
"""
function axspace(A, u::AbstractVector, n::Integer)
    m = checksquare(A)
    B = Matrix{eltype(A)}(undef, m, n)
    B[:, 1] .= u
    for k = 2:n
        B[:, k] .= A * B[:, k-1]
    end
    B
end

function combine_minimals(
    A::AbstractMatrix{R},
    v::AbstractVector{R},
    P::UnivariatePolynomial{R},
    w::AbstractVector{R},
) where R<:Ring
    # P = minimal_polynomial(A, v)
    Q = minimal_polynomial(A, w)
    G = gcd(P, Q)
    PP = P / G
    QQ = Q / G
    g = deg(G)
    H = gcd(G, QQ^g)
    K = G / H
    V = Q * PP
    u = H(A) * v + K(A) * w
    # @assert minimal_polynomial(A, u) == V
    u, V
end

"""
    minimal_polynomial(A::AbstractMatrix)

Calculate the minimal polynomial ``m_A`` of a square matrix `A` over a ring.

``m_A`` is the minimum degree monic polynomial with ``m_A(A) == 0``
"""
function minimal_polynomial(A::AbstractMatrix{R}) where R<:Ring
    _minimal_polynomial(A)[1]
end

# Implementation - also return a generating vector of stable space
function _minimal_polynomial(A::AbstractMatrix{R}) where R<:Ring
    n = checksquare(A)
    u = zeros(R, n)
    v = zeros(R, n)
    PA = similar(A)
    u[1] = 1
    P = minimal_polynomial(A, u)
    PA .= P(A)
    while !iszero(PA)
        k = findfirst(k -> !iszero(view(PA, :, k)), 1:n)
        v[k] = 1
        u, P = combine_minimals(A, u, P, v)
        v[k] = 0
        PA .= P(A)
    end
    P, u
end

struct RNF{R<:Ring}
    minpoly::Vector{<:UnivariatePolynomial{R}}
    trans::Matrix{R}
end
function RNF(p::UnivariatePolynomial{R}, t::AbstractMatrix{R}) where R<:Ring
    RNF{R}([p], t)
end
function RNF(p::Vector{UnivariatePolynomial{R}}, t::AbstractMatrix{R}) where R<:Ring
    RNF{R}(p, t)
end

"""
    rnf_transformation(rnf::RNF)

Return a transformation matrix in the RNF factorization of a square matrix.
The transformation matrices are not unique.
"""
function rnf_transformation(rnf::RNF)
    rnf.trans
end

"""
    rnf_polynomials(rnf::RNF)

Return the sequence of minimal polynomials `P` with `P[1]` multiple of `P[2]` ...
"""
function rnf_polynomials(rnf::RNF)
    rnf.minpoly
end

"""
    rnf_matrix(rnf::RNF)

Return matrix in 'rational normal form' from rnf-factorization of a square matrix.
The form is also known as 'Frobenius normal form' or 'rational canonical form'.
The matrix is a unique block diagonal matrix containing the companion matrices of
the minimal polynomials. See also `rnf_polynomials`.
"""
function rnf_matrix(rnf::RNF{R}) where R
    n = size(rnf.trans, 1)
    M = zeros(R, n, n)
    p = 1
    for pi in rnf.minpoly
        d = deg(pi)
        M[p:p+d-1, p:p+d-1] .= companion(pi)
        p += d
    end
    M
end

function characteristic_polynomial(rnf::RNF)
    prod(rnf_polynomials(rnf))
end

function minimal_polynomial(rnf::RNF)
    first(rnf_polynomials(rnf))
end

# Implementation
function _rational_normal_form(A::AbstractMatrix{R}) where R
    m = checksquare(A)
    P, u = _minimal_polynomial(A)
    r = deg(P)
    lut, _ = lu_axu(A, u)
    piv = lut.pivr
    B = lut.L * lut.U
    B = B[invperm(piv), :]
    if r == m
        return RNF(P, B)
    end
    p1 = view(piv, 1:r)
    p2 = view(piv, r+1:m)
    A12 = A[p1, p2]
    A22 = A[p2, p2]
    L11, L21, U11 = lut.L11, lut.L21, lut.U11
    D = A22 - L21 * (L11 \ A12)

    rnf = rational_normal_form(D)

    B[:, r+1:m] .= B[:, r+1:m] * rnf.trans
    p = r + 1
    for pi in rnf.minpoly
        g = prod_pmv(pi, A, B[:, p])
        h = U11 \ (L11 \ g[p1])
        H = UnivariatePolynomial{R,:x}(h)
        S = H / pi
        B[:, p] .-= S(A) * B[:, 1]
        d = deg(pi)
        for j = p:p+d-2
            B[:, j+1] .= A * B[:, j]
        end
        p += d
    end
    return RNF([P; rnf.minpoly], B)
end

"""
    prod_pvm(p, A, v)

Calculate `p(A) * v` where `p` is a polynomial, `A` a matrix, and `v` an array.
"""
function prod_pmv(p::UnivariatePolynomial, A::AbstractMatrix, v::AbstractArray)
    d = deg(p)
    d < 0 && return zero(v)
    s = p[0] .* v
    for i = 1:d
        v = A * v
        s .+= p[i] .* v
    end
    s
end
