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
    _rational_normal_form(A, category_trait(eltype(A)))
end

"""
    minimal_polynomial(A::AbstractMatrix{F}, u::AbstractVector{F}) where F<:Ring (field)

Calculate the local minimal polynomial `m_A_u` of a square matrix `A` over a ring
for vector `u`.

`m_A_u` is the minimum degree monic polynomial with `m_A_u(A)*u == 0`
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

Calculate the minimal polynomial `m_A` of a square matrix `A` over a ring.

`m_A` is the minimum degree monic polynomial with `m_A(A) == 0`.
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

"""
    transformation(rnf::RNF)

Return a transformation matrix in the RNF factorization of a square matrix.
The transformation matrices are not unique.
"""
function transformation(rnf::RNF)
    rnf.trans
end

"""
    polynomials(rnf::RNF)

Return the sequence of minimal polynomials `P` with `P[1]` multiple of `P[2]` ...
"""
function polynomials(rnf::RNF)
    rnf.minpoly
end

"""
    matrix(rnf::RNF)

Return matrix in 'rational normal form' from rnf-factorization of a square matrix.
The form is also known as 'Frobenius normal form' or 'rational canonical form'.
The matrix is a unique block diagonal matrix containing the companion matrices of
the minimal polynomials. See also `polynomials`.
"""
function matrix(rnf::RNF{R}) where R
    n = size(transformation(rnf), 1)
    M = zeros(R, n, n)
    p = 1
    for pi in rnf.minpoly
        d = deg(pi)
        M[p:p+d-1, p:p+d-1] .= companion(pi)
        p += d
    end
    M
end

function characteristic_polynomial(rnf::Union{RNF,WNF})
    prod(polynomials(rnf))
end

function minimal_polynomial(rnf::RNF)
    first(polynomials(rnf))
end

# Implementation
function _rational_normal_form(A::AbstractMatrix{R}, ::Type{<:FieldTrait}) where R
    m = checksquare(A)
    P, u = _minimal_polynomial(A)
    r = deg(P)
    lut, _ = lu_axu(A, u)
    piv = lut.pivr
    B = lut.L * lut.U
    B = B[invperm(piv), :]
    if r == m
        return RNF([P], B)
    end
    p1 = view(piv, 1:r)
    p2 = view(piv, r+1:m)
    A12 = A[p1, p2]
    A22 = A[p2, p2]
    L11, L21, U11 = lut.L11, lut.L21, lut.U11
    D = A22 - L21 * (L11 \ A12)

    rnf = rational_normal_form(D)

    B[:, r+1:m] .= B[:, r+1:m] * transformation(rnf)
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

"""
    weierstrass_normal_form([rnf,] matrix)

Calculate Weierstrass normal form of a matrix over a field.

If `rnf`is given, it is assumed, that it is the rational normal form of the same matrix.
"""
function weierstrass_normal_form(A::AbstractMatrix{<:Ring})
    _weierstrass_normal_form(A, category_trait(eltype(A)))
end
function weierstrass_normal_form(rnf::RNF, A::AbstractMatrix)
    mini = minimal_polynomial(rnf)
    W = transformation(rnf)
    C = W \ (A * W)
    n1 = 1
    pairs = Pair{typeof(mini),Int}[]
    for p in rnf.minpoly
        n2 = n1 + deg(p) - 1
        D = C[n1:n2, n1:n2]
        plist, V = factor_of_companion(D, p)
        if V != I
            W[:, n1:n2] .= W[:, n1:n2] * V
        end
        append!(pairs, plist)
        n1 = n2 + 1
    end
    return WNF(mini, pairs, W)
end

# assuming A == companion(p)
function factor_of_companion(A::AbstractMatrix, p)
    f = factor(p) # that is the critical operation
    if length(f) <= 1
        return [f[1]], 1I
    end
    W = similar(A, size(A, 1), 0)
    plist = typeof(f[1])[]
    for (q, r) in f
        N = Matrix(nullspace(q(A)^r))
        W = hcat(W, N)
        push!(plist, q => r)
    end
    C = W \ (A * W) # C is block diagonal now
    m1 = 1
    for (q, r) in f
        m2 = m1 + deg(q) * r - 1
        B = C[m1:m2, m1:m2]
        rnf = rational_normal_form(B)
        V = transformation(rnf)
        W[:, m1:m2] .= W[:, m1:m2] * V
        m1 = m2 + 1
    end
    return plist, W
end

function _weierstrass_normal_form(A::AbstractMatrix, ::Type{<:FieldTrait})
    rnf = rational_normal_form(A)
    weierstrass_normal_form(rnf, A)
end

"""
    transformation(rnf::WNF)

Return a transformation matrix in the RNF or WNF factorization of a square matrix.
The transformation matrices are not unique.
"""
function transformation(wnf::WNF)
    wnf.trans
end

"""
    polynomials(rnf::WNF)

Return the sequence of pairs of irreducible polynomials and powers.
"""
function polynomials(wnf::WNF)
    wnf.polyfact
end

"""
    matrix(rnf::WNF)

Return matrix in 'Weierstrass normal form' from wnf-factorization of a square matrix.
The matrix is a block diagonal matrix containing the companion matrices of
powers of irreducible polynomials. See also `wnf_polynomials`. They are factors of the
minimal polynomials for the `rational normal form`.
"""
function matrix(rnf::WNF{R}) where R
    n = size(transformation(rnf), 1)
    M = zeros(R, n, n)
    p = 1
    for (pi, r) in rnf.polyfact
        d = deg(pi) * r
        M[p:p+d-1, p:p+d-1] .= companion(pi^r)
        p += d
    end
    M
end

function minimal_polynomial(wnf::WNF)
    wnf.minpoly
end

"""
    smith_normal_form(matrix)

Calculate Smith normal form including transformation matrices of a matrix over a PID.

Decomposes `S * A * T == D` where `D` is a diagonal matrix.
See also: [`SNF`](@ref)
"""
function smith_normal_form(A::AbstractMatrix{<:Ring})
    _smith_normal_form(A, category_trait(eltype(A)))
end
function _smith_normal_form(
    A::AbstractMatrix{R},
    ::Type{<:PrincipalIdealDomainTrait},
) where R

    m, n = size(A)
    S = zeros(R, m, m) + I
    T = zeros(R, n, n) + I
    B = copy(A)
    k = 1
    while k <= min(m, n) + 1
        n = shift_zero_columns!(B, k, n, T)
        m = shift_zero_rows!(B, k, m, S)
        k > min(m, n) && break
        scol = srow = false
        while !(srow && scol)
            srow = smith_isolate_row!(B, S, k, m, n)
            srow && scol && break
            scol = smith_isolate_col!(B, T, k, m, n)
        end
        k += 1
    end
    @assert m == n
    sort_diagonal!(B, m, S, T)
    SNF([B[i, i] for i = 1:m], S, T)
end

function smith_isolate_row!(A, S, k, m, n)
    stable = true
    colk = view(A, k:m, k) # pivot in this partial column
    x = findfirst(isunit, colk)
    if x === nothing
        x = findfirst(!iszero, colk)
        jk = x + k - 1
        if jk > k
            swap_rows!(A, k, jk, k:n)
            swap_rows!(S, k, jk, axes(S, 2))
            stable = false
        end
        g = A[k, k]
        for j = k+1:m
            h = A[j, k]
            if !iszero(h)
                stable = false
                merge_rows!(A, k, j, k:n, g, h, S)
                g = A[k, k]
                isunit(g) && break
            end
        end
    else # found a unit in A[k,k]
        jk = x + k - 1
        if jk > k
            swap_rows!(A, k, jk, k:n)
            swap_rows!(S, k, jk, axes(S, 2))
            stable = false
        end
        g = A[k, k]
    end
    lc = lcunit(g)
    if !isone(lc)
        A[k, k:n] ./= lc
        S[k, :] ./= lc
        g /= lc
    end
    for j = k+1:m
        h = A[j, k]
        if !iszero(h)
            f = h / g
            add_to_row!(A, f, j, k, k:n)
            add_to_row!(S, f, j, k, axes(S, 2))
        end
    end
    return stable
end

function smith_isolate_col!(A, T, k, m, n)
    stable = true
    x = findfirst(isunit, view(A, k, k:n))
    if x === nothing
        g = A[k, k]
        for j = k+1:n
            h = A[k, j]
            if !iszero(h)
                stable = false
                merge_cols!(A, k, j, k:m, g, h, T)
                g = A[k, k]
                isunit(g) && break
            end
        end
    else # found a unit in A[k,k]
        jk = x + k - 1
        if jk > k
            swap_cols!(A, k, jk, k:m)
            swap_cols!(T, k, jk, axes(T, 1))
            stable = false
        end
        g = A[k, k]
    end
    lc = lcunit(g)
    if !isone(lc)
        A[k:m, k] ./= lc
        T[:, k] ./= lc
        g /= lc
    end
    for j = k+1:n
        h = A[k, j]
        if !iszero(h)
            f = h / g
            add_to_col!(A, f, j, k, k:m)
            add_to_col!(T, f, j, k, axes(T, 1))
        end
    end
    return stable
end

function swap_rows!(A, k, j, r)
    for i in r
        A[k, i], A[j, i] = A[j, i], A[k, i]
    end
end
function swap_cols!(A, k, j, r)
    for i in r
        A[i, k], A[i, j] = A[i, j], A[i, k]
    end
end

function merge_rows!(A, k, j, r, g, h, S)
    c, x, y = gcdx(g, h)
    g /= c
    h /= c
    for i in r
        a = A[k, i]
        b = A[j, i]
        A[k, i] = x * a + y * b
        A[j, i] = -h * a + g * b
    end
    for i in axes(S, 2)
        a = S[k, i]
        b = S[j, i]
        S[k, i] = x * a + y * b
        S[j, i] = -h * a + g * b
    end
end

function merge_cols!(A, k, j, r, g, h, T)
    c, x, y = gcdx(g, h)
    g /= c
    h /= c
    for i in r
        a = A[i, k]
        b = A[i, j]
        A[i, k] = x * a + y * b
        A[i, j] = -h * a + g * b
    end
    for i in axes(T, 1)
        a = T[i, k]
        b = T[i, j]
        T[i, k] = x * a + y * b
        T[i, j] = -h * a + g * b
    end
end

function sort_diagonal!(A, m, S, T)
    while (k = findfirst(i -> !iszero(mod(A[i+1, i+1], A[i, i])), 1:m-1)) !== nothing
        j = k + 1
        g = A[k, k]
        h = A[j, j]
        merge_diagonal!(A, k, j, g, h, S, T)
    end
end

# assume k < j and g == A[k,k] and h == A[j,j]
function merge_diagonal!(A, k, j, g, h, S, T)
    axs = axes(S, 2)
    axt = axes(T, 1)
    if iszero(mod(g, h)) # g divides h: only swap diagonal
        swap_rows!(S, k, j, axs)
        swap_cols!(T, k, j, axt)
        A[j, j] = g
        A[k, k] = h
    else
        c, x, y = gcdx(g, h)
        hh = h / c
        #add_to_col!(A, -one(g), k, j, k:j)
        add_to_col!(T, -one(g), k, j, axt)
        merge_rows!(A, k, j, 1:0, g, h, S)
        #merge_rows!(A, k, j, k:j, g, h, S)
        #add_to_col!(A, y * hh, j, k, k:j)
        add_to_col!(T, y * hh, j, k, axt)
        A[k, k] = c
        A[j, j] = g * hh
    end
end

function add_to_row!(A, f, j, k, r)
    A[j, r] .-= A[k, r] .* f
end

function add_to_col!(A, f, j, k, r)
    A[r, j] .-= A[r, k] .* f
end

function shift_zero_columns!(B, k, n, T)
    a = k
    e = size(T, 2)
    c = n + 1
    while (x = findnext(!iszero, B, CartesianIndex(1, a))) !== nothing
        c = min(x[2], n + 1)
        c > n && break
        r = n - c + 1
        if c > a
            B[:, a:a+r-1] .= B[:, c:n]
            B[:, a+r:n] .= 0
            C = T[:, a:c-1]
            T[:, a:a+e-c] .= T[:, c:e]
            T[:, e-c+a+1:e] .= C
            n -= c - a
        end
        a += 1
        c = n + 1
    end
    return n - c + a
end
function shift_zero_rows!(B, k, m, S)
    a = k
    e = size(S, 1)
    c = m + 1
    while (x = findrow(B, a, k)) !== nothing
        c = min(x, m + 1)
        c > m && break
        r = m - c + 1
        if c > a
            B[a:a+r-1, :] .= B[c:m, :]
            B[a+r:m, :] .= 0
            C = S[a:c-1, :]
            S[a:a+e-c, :] .= S[c:e, :]
            S[e-c+a+1:e, :] .= C
            m -= c - a
        end
        a += 1
        c = m + 1
    end
    return m - c + a
end

function findrow(B, a, k)
    m, n = size(B)
    while a <= m && iszero(view(B, a, k:n))
        a += 1
    end
    a > m ? nothing : a
end


"""
    transformation(rnf::SNF)

Return a transformation matrices in the Smith normal form a matrix.
The transformation matrices are not unique.
"""
function transformation(snf::SNF)
    (snf.trans1, snf.trans2)
end

"""
    matrix(rnf::SNF)

Return matrix in 'Smith normal form' from snf-factorization of a matrix `A`.
The matrix has the same shape as the original matrix, and only the leading diagonal
elements are different from zero.
Each diagonal element divides its successor, if applicable.
"""
function matrix(snf::SNF{R}) where R
    m = size(snf.trans1, 2)
    n = size(snf.trans2, 1)
    M = zeros(R, m, n)
    for i = 1:min(m, n, length(snf.diag))
        M[i, i] = snf.diag[i]
    end
    M
end
