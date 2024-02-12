

export fft!, fft

import Base: length

convolute(a::R, b::R) where R<:Ring = a * b

"""
    fft(n, f::AbstractVector{R}, w::R) where R<:Ring

Calculate Fast Fourier Transform of degree `n` (power of 2) for `f`
(length(f) <= n is filled up with 0).
Given `w` a `n`th principal root of `R(1)`. (`w^n == 1` && w^(n/2) == -1)`.
For efficiency reasons, w may be substituted by precalculated `[1, w, w^2, ..., w^(n/2-1)]`.
"""
fft(n::Integer, f::AbstractVector{R}, w::R) where R<:Ring = fft2(n, f, [1, w])

function fft2(n::Integer, f::AbstractVector{R}, w::AbstractVector{R}) where R<:Ring
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
    return butterfly!(F, 1, n)
end

function fft3(n::Integer, x::AbstractVector{R}, w::R) where R<:Ring
    if n == 1
        return x
    end
    k = ilog3(n)
    3^k == n || throw(ArgumentError("$n != $(3^k) must be a power of 3"))
    w^n == 1 || throw(ArgumentError("$w must be a $n-th root of unity"))
    # Extact the even indices from array.
    n3 = n ÷ 3
    w^n3 != 0 || throw(ArgumentError("$w must not be a $(n3)-th root of unity"))
    w3 = w^3
    W = w^n3
    W2 = W * W

    y_0 = fft3(n3, x[1:3:n], w3)
    y_1 = fft3(n3, x[2:3:n], w3)
    y_2 = fft3(n3, x[3:3:n], w3)

    y = similar(x)
    omega = one(w)
    n6 = n3 + n3
    for k = 1:n3
        y0 = y_0[k]
        y1 = y_1[k] * omega
        y2 = y_2[k] * omega^2
        y[k] = y0 + y1 + y2
        y[k+n3] = y0 + W * y1 + W2 * y2
        y[k+n6] = y0 + W2 * y1 + W * y2
        omega *= w
    end
    return y
end

function ffthf(n::Integer, f::AbstractVector{R}, w::AbstractVector{R}) where R<:Ring
    m = length(f)
    F = copy(f)
    if n > m
        fill_end!(F, n, 0)
    end
    isone(w[1]) || throw(ArgumentError("w[1] must be one"))
    M = firstprime(n)
    N = n ÷ M
    W = w[2]^N
    iszero(W^M - 1) || throw(ArgumentError("w^$n must be one"))
    isunit(W - 1) || throw(ArgumentError("w^$N - 1 must be unit"))
    for j = length(w)+1:n
        resize!(w, n)
        w[j] = w[j-1] * w[2]
    end
    L = 1
    while L < n
        for base = 1:n÷L:n
            for j = 0:N-1
                dftf!(F, L, N, Val(M), j, base, w)
            end
        end
        L *= M
        M = firstprime(N)
        N ÷= M
    end
    return F
end

function dftf!(F, L, N, ::Val{M}, j, base, w) where M
    n = L * M * N
    @assert n == length(w)
    ω(x) = w[mod(x, n)+1]
    f = tuple((F[base+j+k*N] for k = 0:M-1)...)

    rNL = zero(L)
    rjL = zero(L)
    NL = N * L
    jL = j * L
    for r = 0:M-1
        s = f[1]
        #print("N=$N: F'[$base+$j+$(r)N] = (F[$base+$j+$(0)N] ")
        rkNL = rNL
        for k = 1:M-1
            s += f[k+1] * ω(rkNL)
            #print("+ F[$base+$j+$(k)N] * $(ω(rkNL)) ")
            rkNL += rNL
        end
        F[base+j+r*N] = s * ω(rjL)
        #println(") * $(ω(rjL))")
        rNL += NL
        rjL += jL
    end
    nothing
end

function ffthb(n::Integer, f::AbstractVector{R}, w::AbstractVector{R}) where R<:Ring
    m = length(f)
    F = copy(f)
    if n > m
        fill_end!(F, n, 0)
    end
    isone(w[1]) || throw(ArgumentError("w[1] must be one"))
    M = lastprime(n)
    N = 1
    L = n ÷ M
    W = w[2]^L
    iszero(W^M - 1) || throw(ArgumentError("w^$n must be one"))
    isunit(W - 1) || throw(ArgumentError("w^$L - 1 must be unit"))
    for j = length(w)+1:n
        resize!(w, n)
        w[j] = w[j-1] * w[2]
    end
    while N < n
        for base = 1:n÷L:n
            for j = 0:N-1
                dftb!(F, L, N, Val(M), j, base, w)
            end
        end
        N *= M
        M = lastprime(L)
        L ÷= M
    end
    return F
end

function dftb!(F, L, N, ::Val{M}, j, base, w) where M
    n = L * M * N
    @assert n == length(w)
    ω(x) = w[mod(n - x, n)+1]

    rNL = zero(L)
    rjL = zero(L)
    NL = N * L
    jL = j * L
    f = tuple((F[base+j+k*N] * ω(k * jL) for k = 0:M-1)...)
    for r = 0:M-1
        s = f[1]
        #print("LMN=$L $M $N: F'[$base+$j+$(r)N] = (F[$base+$j+$(0)N] ")
        rkNL = rNL
        for k = 1:M-1
            s += f[k+1] * ω(rkNL)
            #print("+ F[$base+$j+$(k)N] * $(ω(j*k*L)) * $(ω(rkNL)) ")
            rkNL += rNL
        end
        F[base+j+r*N] = s
        #println(")")
        rNL += NL
        rjL += jL
    end
    nothing
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
    return butterfly!(F, dd, n)
end

"""
    schoenhage_strassen_algo(P, Q, n::Integer)

For polynomials `P` and `Q` with degree `< n` calculate `P * Q mod x^n + 1`.
The element type of `P` and `Q` must have invertible `2`.

`n` must be a power of `2` or `0`, in latter case the smallest possible value is calculated.

Only the principle of the algorithm is demonstrated.
The implementation does not allow the estimated efficiency gains.
"""
function schoenhage_strassen_algo(
    F::P,
    G::P,
    n::Integer,
) where {R<:Ring,P<:UnivariatePolynomial{R}}
    characteristic(R) == 0 || isunit(R(2)) || throw(ArgumentError("R(2) must be inverible"))
    dF = deg(F)
    dG = deg(G)
    n = n <= 0 ? 2^(ilog2(dF + dG) + 1) : n
    @assert count_ones(n) == 1 "$n must be a power of 2"
    max(dF, dG) < n || throw(ArgumentError("degrees for F and G must both be < $n"))
    N = 2^(ilog2(2n - 1) + 1)
    @assert N >= 2n - 1
    N2 = isqrt(N)
    N1H = N ÷ N2
    N1 = N1H * 2
    @assert N1H * N2 == N

    X = monom(P)
    B = Quotient(P, X^N1 + 1) # avoid P / (x^N1 + 1) which implies irreducibility check
    FF = [B(F[di:di+N1H-1]) for di = 0:N1H:n-1]
    GG = [B(G[di:di+N1H-1]) for di = 0:N1H:n-1]
    Ψ = B(X)^(2N1 ÷ N2)
    FQ = fft(N2, FF, Ψ)
    GQ = fft(N2, GG, Ψ)

    HQ = FQ .* GQ # should be recursive call to obtain efficiency!
    HH = fft(N2, HQ, inv(Ψ))

    H = value.(HH) / N2
    Y = X^N1H
    sum(H[i+1] * Y^i for i = 0:N2-1)
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
function revert(a::Integer, n::Integer)
    accu = (a >> UInt8(n)) << UInt8(n)
    for i = 1:n
        accu += accu
        accu += isodd(a)
        a >>= 0x1
    end
    accu
end

"""
    revert(a::Int, v::Vector)

Represent `a` in a digit system given by `v`, revert positions and return "reverse" of `a`.
"""
function revert(a::Integer, v::Vector{T}) where {T<:Integer}
    n = length(v)
    resize!(v, 2n)
    for i = 1:n
        a, v[i+n] = divrem(a, v[i])
    end
    for i = 1:n
        a = a * v[i] + v[i+n]
    end
    resize!(v, n)
    a
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

struct Comb
    comb::Vector{Int}
end

Base.length(c::Comb) = prod(c.comb)

Base.iterate(c::Comb) = begin
    z = zeros(Int, length(c.comb))
    z, z
end

function Base.iterate(c::Comb, s)
    l = findlast(i -> s[i] < c.comb[i] - 1, axes(s, 1))
    l === nothing && return l
    s = copy(s)
    s[l] += 1
    s[l+1:end] .= 0
    s, s
end

"""
    bestpowers(n::Integer, p::Vector{Integer})

Calculate the smallest number `m >= n`, which is a product of integral powers of the
elements of `p`.
"""
function bestpowers(n::T, p::Vector) where T<:Integer
    p = T.(sort(p; rev = true))
    pe = p[end]
    tm = Base.hastypemax(T) ? typemax(T) : T(0)
    nm = tm ÷ pe + 1
    n <= nm || iszero(tm) || throw(ArgumentError("n must be < $nm"))
    m = ilog.(p, n - 1) .+ 1
    lp = log.(p)
    lpe = lp[end]
    vbest = tm
    lm = iszero(tm) ? typemax(float(T)) : log(vbest)
    for i in axes(p, 1)
        if m[i] * log(p[i]) < lm
            z = p[i]^m[i]
            if z < vbest || iszero(vbest)
                vbest = z
                lm = log(vbest)
            end
        end
    end
    comb = Comb(m[1:end-1])
    for i in comb
        lz = sum(lp[1:end-1] .* i)
        if lz >= lm
            k = findlast(!iszero, i)
            i[k] = m[k]
            continue
        end
        z = T(prod(p[1:end-1] .^ i))
        if z < n
            k = ilog(pe, n ÷ z)
            # println("$n $z $k lm=$lm $lz")
            z *= pe^k
            lz += lpe * k
        end
        while z < n && lz < lm
            z *= pe
            lz += lpe
        end
        if z < vbest && lz < lm
            vbest = z
        end
    end
    vbest
end

import Primes

function firstprime(f::Primes.Factorization)
    i = findfirst(x -> last(x) > 0, f.pe)
    i === nothing ? 1 : first(f.pe[i])
end

function firstprime(n::Integer)
    firstprime(factor(abs(n)))
end

function lastprime(f::Primes.Factorization)
    i = findlast(x -> last(x) > 0, f.pe)
    i === nothing ? 1 : first(f.pe[i])
end

function lastprime(n::Integer)
    lastprime(factor(abs(n)))
end
