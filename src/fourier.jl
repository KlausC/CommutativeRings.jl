

export fft!, fft


convolute(a::R, b::R) where R<:Ring = a * b

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
        fill_end!(F, n, 0)
    end
    isone(w[1]) || throw(ArgumentError("w[1] must be one"))
    iszero(w[2]^(n ÷ 2) + 1) || throw(ArgumentError("w^($(n)/2) must be -1"))
    for j = length(w)+1:n÷2
        resize!(w, n ÷ 2)
        w[j] = convolute(w[j-1], w[2])
    end

    m = n
    d = 1
    while m > 1
        k = m ÷ 2
        for j = 1:m:n
            for i = 0:k-1
                Fi, Fik = F[i+j], F[i+k+j]
                F[i+j] = Fi + Fik
                F[i+k+j] = convolute((Fi - Fik), w[i*d+1])
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
    fft!(n, F:Vector{R}, dd, z, W::Vector) where R

Special case of fft over the quotient ring `R[X]/(X^dd + 1)` for `n` and `dd` powers of 2,
using principal `2dd`th root of unity `ω = X^z, ω^dd == -1`.

Result overwrites input `F`. `W` is workspace of same size as `F`. Assume `n * dd == length(F)`.
"""
function fft!(n::Integer, F::V, dd::Int, z::Int) where {R,V<:AbstractVector{R}}
    n > 0 && count_ones(n) == 1 || throw(ArgumentError("n must be power of 2"))
    0 < dd && count_ones(dd) == 1 || throw(ArgumentError("dd must be power of 2 < n"))
    length(F) == n * dd || throw(ArgumentError("length(F) must be n * dd"))
    #mod(z * n ÷ 2, 2dd) == dd || throw(ArgumentError("w^($(n)/2) must be -1"))

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
                convolute_j!(F, (i + k + j) * dd, dd, i * d * z)
            end
        end
        m = k
        d += d
    end
    butterfly!(F, dd, n)
    F
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
    # characteristic(R) != 2 || throw(ArgumentError("R must not have characteristic 2"))
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

"""
    schoenhage_strassen(F, G, n)

Calculate product of polynomials with coefficients `F` and `G`, both with degree `< n`.
Return result modulo `x^n + 1`.
The size of the result vector is reduced to minimum.

Allocates working space of `3 * 2n`.
"""
function schoenhage_strassen(F::AbstractVector{R}, G::AbstractVector{R}, n::Int) where R

    characteristic(R) == 0 || isunit(R(2)) || throw(ArgumentError("2 has inverse in R"))
    dF = deg(F)
    dG = deg(G)
    (dF < 0 || dG < 0) && n <= 0 && (n = 1)
    n = n <= 0 ? 2^(ilog2(dF + dG) + 1) : n
    max(dF, dG) < n || throw(ArgumentError("degrees for F and G must both be < $n"))

    FF = similar(F, 2n)
    GG = similar(G, 2n)
    W = similar(F, 2n)
    v, m = schoenhage_strassen!(F, G, n, FF, GG, W)
    m = something(findlast(!iszero, view(v, 1:m)), 0)
    resize!(v, m)
end

"""
    schoenhage_strassen(F, G, n, FF, GG, W) -> (FF, m)

Like `shoenhage_strassen(F, G, n)` but using preallocated working spaces `FF, GG, W`.
On return `FF` is keeping the compete result, while `F[1:m]` is the result.
"""
function schoenhage_strassen!(F, G, n, FF, GG, W)
    k = ilog2(n)
    d = 2^(k ÷ 2)
    δ = 2^(k - k ÷ 2)
    @assert n == d * δ # = 2^k
    insert_zeros!(FF, F, 0, n, d)
    insert_zeros!(GG, G, 0, n, d)
    _schoenhage_strassen!(k, FF, GG, W)
end

function _schoenhage_strassen!(k::Int, FF::Q, GG::Q, W::Q) where Q<:AbstractVector
    d = 2^(k ÷ 2)
    δ = 2^(k - k ÷ 2)
    z = isodd(k) ? 1 : 2
    w = 2z

    scale!(FF, 2d, z)
    scale!(GG, 2d, z)
    fft!(δ, FF, 2d, w)
    fft!(δ, GG, 2d, w)
    convolute_all!(FF, FF, GG, 2d, W)
    fft!(δ, FF, 2d, -w)
    scale!(FF, 2d, -z)
    for l in axes(FF, 1)
        FF[l] = sdiv(FF[l], δ)
    end
    shrink!(FF, d, δ)
end

"""

Multiply by `x^(z*j)` modulo `x^n + 1` all polynomials `F[j*n+1:j*n+n]` contained in `F`.
"""
function scale!(F::AbstractVector, n::Int, z::Int)
    x = z
    for jn = n:n:length(F)-1
        convolute_j!(F, jn, n, x)
        x += z
    end
    F
end

"""
    shrink!(A, d, δ)

Reduce size of `A` from orinally `2*d*δ` to `d*δ` by adding chunks `A[j*2d+1:j*2d+2d]`
to `A[j*d+1:j*d+2d]` for `j ∈ 0:δ-1`. Special treatment of last `d` to relize
multiplication modulo `x^(d*δ) + 1`.
"""
function shrink!(A, d, δ)
    length(A) >= 2d * δ || throw(ArgumentError("length of B"))
    length(A) >= d * δ || throw(ArgumentError("length of A"))
    n = d * δ
    δ <= 1 && return A, n
    for i = d:d:n-2d
        for l = 1:d
            A[i+l] += A[2i+l]
            A[i+d+l] = A[2i+d+l]
        end
    end
    for l = 1:d
        A[n-d+l] += A[2n-2d+l]
        A[l] -= A[2n-d+l]
    end
    return A, n
end

"""
    convolute_j!(p::Vector, jn, n, z)

Multiply in place polynomial of degree `n-1` by `x^z` modulo `x^n + 1`.

The polynomial is given by `sum^n-1_i=0 p[i+jn+1] * x^i`.
Assume `0 <= jn < length(p) - n`.
"""
function convolute_j!(p::AbstractArray, jn::Int, n::Int, z::Int)
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

"""
    convolute_all!(r, a, b, n, w)

Multiply pairwise polynomials modulo `x^n + 1`.

`a[j*n+1:j*n+n] and b[j*n+1:j*n+n]` contain the coefficients of the source polynomials,
`r[j*n+1:j*n+n]` of the results.
`w` is additional workspace of same size as `a`, `b`, and `r`.
`r` may be identical to `a` (but not `b`).
If length is not a multiple of `n`, results are undefined.
"""
function convolute_all!(r::P, a::P, b::P, n::Int, w::P) where P<:AbstractVector
    if n < 2^20
        convolute_naive!(r, a, b, n, w)
    else
        convolute_rec!(r, a, b, n, w)
    end
end

function convolute_naive!(r::P, a::P, b::P, n::Int, w::P) where P<:AbstractVector
    copy!(w, a)
    fill!(r, 0)

    for jn = 0:n:length(a)-1
        for i = 0:n-1
            bi = b[i+jn+1]
            if !iszero(bi)
                for k = jn+1:jn+n
                    r[k] += w[k] * bi
                end
            end
            convolute_j!(w, jn, n, 1)
        end
    end
    return r
end

"""
    insert_zeros!(FF, F, j, n, d)

Fill vector `FF` of length `2n` with chunks `[F[j*n+1:j*n+d]; zeros(d)]...` taken form `F`.
If length of `F` is not sufficient, it is virtually filled with zeros.
"""
function insert_zeros!(FF::AbstractVector, F::AbstractVector, j::Int, n::Int, d::Int)
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
sdiv(a, b) = sdiv(promote(a, b)...)

function deg(F::AbstractVector)
    f = findlast(!iszero, F)
    return (f === nothing ? 0 : f) - 1
end

function ord(F::AbstractVector)
    f = findfirst(!iszero, F)
    return (f === nothing ? 1 : f) - 1
end

e_factor = Ref(200)

function convolute(F::AbstractVector{R}, G::AbstractVector{R}) where R
    convolute!(R[], F, G)
end

function convolute!(
    H::AbstractVector{R},
    F::AbstractVector{R},
    G::AbstractVector{R},
) where R
    dF, dG = deg(F), deg(G)
    min(dF, dG) < 0 && return resize!(H, 0)
    N = 2^(ilog2(min(dF, dG)) + 1)
    resize!(H, max(dF, dG) + N + 1)
    m = dF + dG + 1
    convolute_noresize!(H, F, G)
    resize!(H, m)
end

function convolute_noresize!(H::AbstractVector{R}, F, G) where R
    dF, dG = deg(F), deg(G)
    (dF < 0 || dG < 0) && return H
    e1, opt = effort_naive(F, G)
    e2 = effort_mixed(dF + 1, dG + 1)
    if e1 <= e2
        convolute_naive!(H, F, G, opt)
    else
        convolute_mixed!(H, F, G)
    end
end

function convolute_naive!(H, F, G, Fless::Bool)
    dF = deg(F)
    dG = deg(G)
    @assert !(dF < 0 || dG < 0)
    @assert length(H) >= dF + dG + 1
    fill!(H, 0)
    if Fless
        for i = 0:dF
            fi = F[i+1]
            if !iszero(fi)
                for j = 0:dG
                    H[j+i+1] += fi * G[j+1]
                end
            end
        end
    else
        for i = 0:dG
            gi = G[i+1]
            if !iszero(gi)
                for j = 0:dF
                    H[j+i+1] += F[j+1] * gi
                end
            end
        end
    end
    H
end

function convolute_mixed!(H, F, G)
    dF, dG = deg(F), deg(G)
    N = 2^(ilog2(min(dF, dG)) + 1)
    n = 2N
    @assert length(H) >= max(dF, dG) + N
    fill!(H, 0)
    FF = similar(F, 2n)
    GG = similar(G, 2n)
    W = similar(F, 2n)
    if max(dF, dG) + 1 <= N
        FG, m = schoenhage_strassen!(F, G, n, FF, GG, W)
        @assert m <= length(H)
        for j = 1:m
            H[j] = FG[j]
        end
        return H
    end
    if dF <= dG
        M = mod(dG + 1, N)
        convolute_noresize!(H, F, view(G, 1:M))
        for i = M+1:N:dG
            FG, m = schoenhage_strassen!(F, view(G, i:i-1+N), n, FF, GG, W)
            for j = 1:m
                H[j+i-1] += FG[j]
            end
        end
    else
        M = mod(dF + 1, N)
        convolute_noresize!(H, view(F, 1:M), G)
        for i = M+1:N:dF
            FG, m = schoenhage_strassen!(view(F, i:i-1+N), G, n, FF, GG, W)
            for j = 1:m
                H[j+i-1] += FG[j]
            end
        end
    end
    H
end


function effort_naive(F, G)
    dF, dG = deg(F), deg(G)
    (dF < 0 || dG < 0) && return 0, false
    nzF = count(!iszero, F)
    nzG = count(!iszero, G)
    nf = nzF * (dG + 1)
    ng = nzG * (dF + 1)
    min(nf, ng), nf <= ng
end

function effort_mixed(n, m)
    n, m = extrema((n, m))
    if n <= 1
        max(n * m, 0)
    else
        N = 2^(ilog2(n - 1) + 1)
        M = max(m ÷ N, 1)
        effort_sch(N) * M + effort_noresize(max(m - N * M, 0), n)
    end
end

function effort_noresize(n, m)
    if n > 0 && m > 0
        min(n * m, effort_mixed(n, m))
    else
        0
    end
end

function effort_sch(N)
    (N * ilog2(N) + 1) * e_factor[]
end

"""
    revert(a::Int, b::Int)

Return `a` with bits `0:n-1` in reverse order.
"""
function revert(a, n)
    accu = (a >> UInt8(n)) << UInt8(n)
    for i = 1:n
        accu += accu
        accu += isodd(a)
        a >>= 0x1
    end
    accu
end

"""
    butterfly!(a, d, k)

Permute in-memory so `a_new[revert(i)*d+l] == a[i*d] for i ∈ 0:2^k-1 for l ∈ 1:d`.
"""
function butterfly!(F::AbstractVector, dd::Int, n::Int)
    k = ilog2(n)
    @assert n * dd == length(F)
    id = 0
    for i = 0:n-1
        j = revert(i, k)
        if i < j
            jd = j * dd
            for l = 1:dd
                F[id+l], F[jd+l] = F[jd+l], F[id+l]
            end
        end
        id += dd
    end
    F
end
