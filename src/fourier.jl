

export fft!, fft

length(f) = Base.length(f)

multiply(a::R, b::R) where R<:Ring = a * b

"""
    fft(n, f::AbstractVector{R}, w::R) where R<:Ring

Calculate Fast Fourier Transform of degree `n` (power of 2) for `f`
(length(f) <= n is filled up with 0).
Given `w` a `n`th principal root of `R(1)`. (`w^n == 1` && w^(n/2) == -1)`.
For efficiency reasons, w may be substituted by precalculated `[1, w, w^2, ..., w^(n/2-1)]`.
"""
fft(n::Integer, f::AbstractVector{R}, w::R) where R<:Ring = fft(n, f, [1, w])

function fft(n::Integer, f::AbstractVector{R}, w::AbstractVector{R}) where R<:Ring
    n > 0 && count_ones(n) == 1 || throw(ArgumentError("n must be power of 2"))
    m = length(f)
    F = copy(f)
    if n > m
        resize!(F, n)
        F[m+1:n] .= zero(R)
    end
    isone(w[1]) || throw(ArgumentError("w[1] must be one"))
    iszero(w[2]^(n ÷ 2) + 1) || throw(ArgumentError("w^($(n)/2) must be -1"))
    for j = length(w)+1:n÷2
        resize!(w, n ÷ 2)
        w[j] = multiply(w[j-1], w[2])
    end

    m = n
    d = 1
    while m > 1
        k = m ÷ 2
        for j = 1:m:n
            for i = 0:k-1
                Fi, Fik = F[i+j], F[i+k+j]
                F[i+j] = Fi + Fik
                F[i+k+j] = multiply((Fi - Fik), w[i*d+1])
            end
        end
        m = k
        d += d
    end
    G = similar(F)
    m = 2
    while m <= n
        k = m ÷ 2
        for j = 1:m:n
            for i = 0:k-1
                G[2i+j] = F[i+j]
                G[2i+j+1] = F[i+k+j]
            end
        end
        F, G = G, F
        m += m
    end
    F
end

"""
    fft!(n, F:Vector{R}, dd, z, G::Vector) where R

Special case of fft over the quotient ring `R[X]/(X^dd + 1)` for `n` and `dd` powers of 2,
using principal `2dd`th root of unity `ω = X^z, ω^dd == -1`.

Result overwrites input `F`. `G` is workspace of same size as `F`. Assume `n * dd == length(F)`.
"""
function fft!(n::Integer, F::V, dd::Int, z::Int, G::V) where {R,V<:AbstractVector{R}}
    n > 0 && count_ones(n) == 1 || throw(ArgumentError("n must be power of 2"))
    0 < dd && count_ones(dd) == 1 || throw(ArgumentError("dd must be power of 2 < n"))
    length(F) == n * dd || throw(ArgumentError("length(F) must be n * dd"))
    mod(z * n ÷ 2, 2dd) == dd || throw(ArgumentError("w^($(n)/2) must be -1"))

    F0 = F
    m = n
    d = 1
    while m > 1
        k = m ÷ 2
        for j = 0:m:n-1
            for i = 0:k-1
                ijd = (i + j) * dd
                ikd = (i + k + j) * dd
                for l = 1:dd
                    Fij = F[ijd+l]
                    Fik = F[ikd+l]
                    F[ijd+l] = Fij + Fik
                    F[ikd+l] = Fij - Fik
                end
                multiply!(F, (i + k + j) * dd, dd, i * d * z)
            end
        end
        m = k
        d += d
    end
    m = 2
    while m <= n
        k = m ÷ 2
        for j = 0:m:n-1
            for i = 0:k-1
                for l = 1:dd
                    G[(2i+j)*dd+l] = F[(i+j)*dd+l]
                    G[(2i+j+1)*dd+l] = F[(i+k+j)*dd+l]
                end
            end
        end
        F, G = G, F
        m += m
    end
    if F !== F0
        F0 .= F
    end
    F0
end

"""
    schoenhage_strassen_algo(P, Q, n::Integer)

For polynomials `P` and `Q` calculate `P * Q mod x^n + 1`.
The element type of `P` and `Q` must have invertible `2`.

Only the principle of the algorithm is demonstrated.
The implementation does not allow the estimated efficiency gains.
"""
function schoenhage_strassen_algo(
    F::P,
    G::P,
    n::Integer,
) where {R<:Ring,P<:UnivariatePolynomial{R}}
    characteristic(R) != 2 || throw(ArgumentError("R must not have characteristic 2"))
    dF = deg(F)
    dG = deg(G)
    n = n <= 0 ? 2^(ilog2(dF + dG) + 1) : n
    max(dF, dG) < n || throw(ArgumentError("degrees for F and G must both be < $n"))
    k = ilog2(n)
    d = 2^(k ÷ 2)
    δ = 2^(k - k ÷ 2)
    @assert n == d * δ # = 2^k

    X = monom(P)
    B = Quotient(P, X^(2 * d) + 1) # avoid P / (x^2d +1) which implies irreducibility check
    FF = [B(F[di:di+d-1]) for di = 0:d:n-1]
    GG = [B(G[di:di+d-1]) for di = 0:d:n-1]
    w = B(X)^2
    FQ = fft(2d, FF, w)
    GQ = fft(2d, GG, w)

    HQ = FQ .* GQ # should be recursive call to obtain efficiency!
    HH = fft(2d, HQ, inv(w))

    H = value.(HH) / (2d)
    Y = X^d
    sum(H[i+1] * Y^i for i = 0:δ-1)
end

function schoenhage_strassen(F::P, G::P, n::Int) where {R,P<:AbstractVector{R}}

    characteristic(R) != 2 || throw(ArgumentError("R has characteristic 2"))
    dF = deg(F)
    dG = deg(G)
    (dF < 0 || dG < 0) && n <= 0 && (n = 1)
    n = n <= 0 ? 2^(ilog2(dF + dG) + 1) : n
    max(dF, dG) < n || throw(ArgumentError("degrees for F and G must both be < $n"))

    FF = similar(F, 2n)
    GG = similar(G, 2n)
    W = similar(F, 2n)
    _schoenhage_strassen!(F, G, 0, n, FF, GG, W)

end
function _schoenhage_strassen!(
    F::P,
    G::P,
    j::Int,
    n::Int,
    FF::P,
    GG::P,
    W::P,
) where P<:AbstractVector

    k = ilog2(n)
    d = 2^(k ÷ 2)
    δ = 2^(k - k ÷ 2)
    @assert n == d * δ # = 2^k

    z = isodd(k) ? 1 : 2
    w = 2z
    insert_zeros!(FF, F, j, n, d)
    insert_zeros!(GG, G, j, n, d)
    scale!(FF, 2d, z)
    scale!(GG, 2d, z)
    fft!(δ, FF, 2d, w, W)
    fft!(δ, GG, 2d, w, W)
    multiply!(FF, FF, GG, 2d, W)
    fft!(δ, FF, 2d, -w, W)
    scale!(FF, 2d, -z)
    FF .= sdiv.(FF, δ)
    shrink!(W, FF, d, δ)
end

"""

Multiply by `x^(z*j)` modulo `x^n + 1` all polynomials `F[j*n+1:j*n+n]` contained in `F`.
"""
function scale!(F::AbstractVector, n::Int, z::Int)
    x = z
    for jn = n:n:length(F)-1
        multiply!(F, jn, n, x)
        x += z
    end
    F
end

function shrink!(A, B, d, δ)
    length(B) >= 2d * δ || throw(ArgumentError("length of B"))
    length(A) >= d * δ || throw(ArgumentError("length of A"))
    n = d * δ
    A[1:2d] .= B[1:2d]
    for i = d:d:n-2d
        A[i+1:i+d] .+= B[2i+1:2i+d]
        A[i+d+1:i+2d] .= B[2i+d+1:2i+2d]
    end
    A[n-d+1:n] .+= B[2n-2d+1:2n-d]
    A[1:d] .-= B[2n-d+1:2n]
    resize!(A, n)
end

"""
    multiply!(p::Vector, jn, n, z)

Multiply in place polynomial of degree `n-1` by `x^z` modulo `x^n + 1`.

The polynomial is given by `sum^n-1_i=0 p[i+jn+1] * x^i`.
Assume `0 <= jn < length(p) - n`.
"""
function multiply!(p::AbstractArray, jn::Int, n::Int, z::Int)
    @assert 0 <= jn <= length(p) - n
    jn += 1
    z = mod(z, 2n)
    g = gcd(n, z)
    ng = n ÷ g
    for i = 0:g-1
        s = i
        x = p[jn+i]
        for ii = 1:ng
            t = s + z
            if t >= n
                t -= n
                if t >= n
                    t -= n
                else
                    x = -x
                end
            end
            jnt = jn + t
            x, p[jnt] = p[jnt], x
            s = t
        end
    end
    return p
end
export multiply!

"""
    multiply!(r, a, b, n, w)

Multiply pairwise polynomials modulo `x^n + 1`.

`a[j*n+1:j*n+n] and b[j*n+1:j*n+n]` contain the coefficients of the source polynomials,
`r[j*n+1:j*n+n]` of the results.
`w` is additional workspace of same size as `a`, `b`, and `r`.
`r` may be identical to `a` (but not `b`).
If length is not a multiple of `n`, results are undefined.
"""
function multiply!(r::P, a::P, b::P, n::Int, w::P) where P<:AbstractVector
    w .= a
    fill!(r, 0)

    for jn = 0:n:length(a)-1
        for i = 0:n-1
            bi = b[i+jn+1]
            for k = jn+1:jn+n
                r[k] += w[k] * bi
            end
            multiply!(w, jn, n, 1)

        end
    end
    return r
end

"""
    insert_zeros!(FF, F, j, n, d)

Return a vector of length `2n` composed of `[F[j*n+1:j*n+d]; zeros(d)]...`
multiplied in place by `x^(z*k)` modulo `x^2d + 1`.
"""
function insert_zeros!(FF::V, F::V, j::Int, n::Int, d::Int) where V<:AbstractVector
    mod(n, d) == 0 || throw(ArgumentError("d must divide n"))
    m = length(F)
    fill!(FF, 0)
    kdj = j * n
    for k = 0:n÷d-1
        kdj2 = kdj + kdj
        for i = 1:min(d, m - kdj)
            FF[kdj2+i] = F[kdj+i]
        end
        kdj += d
    end
    return FF
end

function fill_end!(dest::Vector{T}, n::Integer, x) where T
    m = lastindex(dest)
    resize!(dest, n)
    if n > m
        x isa UndefInitializer && return dest
        xT = convert(T, x)::T
        for i = m+1:lastindex(dest)
            dest[i] = xT
        end
    end
    return dest
end

sdiv(a::R, b::R) where R<:Ring = a / b
sdiv(a::R, b::R) where R<:Integer = iszero(rem(a, b)) ? div(a, b) : throw(DivideError())

function deg(F::AbstractArray)
    f = findlast(!iszero, F)
    return (f === nothing ? 0 : f) - 1
end
