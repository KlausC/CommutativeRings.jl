
export fft!, fft2, ffthf, ffthb

import Base: length

convolute(a::R, b::R) where R<:Ring = a * b

"""
    fft2(n, f::AbstractVector{R}, w::R) where R<:Ring

Calculate Fast Fourier Transform of degree `n` (power of 2) for `f`
(length(f) <= n is filled up with 0).
Given `w` a `n`th principal root of `R(1)`. (`w^n == 1` && w^(n/2) == -1)`.
For efficiency reasons, w may be substituted by precalculated `[1, w, w^2, ..., w^(n/2-1)]`.
"""
fft2(n::Integer, f::AbstractVector{R}, w::R) where R<:Ring = fft2(n, f, [1, w])

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
    return butterfly2!(F, 1, n)
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

ffthf(n, f, w::Ring) = ffthf(n, f, [1, w])
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

ffthb(n, f, w::Ring) = ffthb(n, f, [1, w])
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
    return butterfly2!(F, dd, n)
end

"""
    allpf(n::Integer)

Return ordered vector of prime factors of `n`.
"""
allpf(n) = vcat((ones(Int, x) * p for (p, x) in factor(n))...)

"""
    revert(a::Int, b::Int)

Return `a` with bits `0:n-1` in reverse order.
"""
function revert(a::Integer, n::Integer)
    b = zero(a)
    for i = 1:n
        b += b
        b += isodd(a)
        a >>= 0x1
    end
    a << UInt8(n) + b
end

"""
    revert(a::Int, n::Int, base::Int)

Represent `a` in a n-digit system given by `base`, revert positions and return "reverse" of `a`.
"""
function revert(a::Integer, n::Int, base::Int)
    b = zero(a)
    for i = 1:n
        vi = base
        b *= vi
        if a != 0
            a, w = divrem(a, vi)
            b += w
        end
    end
    a == 0 ? b : a * base^n + b
end

"""
    revert(a::Int, v::Vector)

Represent `a` in a digit system given by `v`, revert positions and return "reverse" of `a`.
"""
function revert(a::Integer, v::Union{AbstractVector,Tuple})
    b = zero(a)
    for i = 1:length(v)
        vi = v[i]
        b *= vi
        if a != 0
            a, w = divrem(a, vi)
            b += w
        end
    end
    a == 0 ? b : a * prod(v) + b
end

"""
    butterfly2!(a, d, k)

Permute in-memory so `a_new[revert(i, ilog2(n))*d+l] == a[i*d] for i ∈ 0:n-1 for l ∈ 1:d`.
"""
function butterfly2!(F::AbstractVector, dd::Int, n::Int)
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

function butterflyf!(F::AbstractVector, d::Int, n::Int)
    count_ones(n) == 1 ? butterfly2!(F, d, n) : butterfly!(F, d, allpf(n))
end
function butterflyb!(F::AbstractVector, d::Int, n::Int)
    count_ones(n) == 1 ? butterfly2!(F, d, n) : butterfly!(F, d, reverse(allpf(n)))
end

function butterfly!(F::AbstractVector, d::Int, pf::AbstractVector)
    n = prod(pf)
    @assert n * d == length(F)
    bits = falses(n)
    for i = 0:n-1
        k = revert(i, pf)
        (k <= i || bits[k+1]) && continue
        j = i
        jd = j * d
        s = tuple(view(F, jd+1:jd+d)...)
        while k != i
            bits[k+1] = 1
            kd = k * d
            for l = 1:d
                F[jd+l] = F[kd+l]
            end
            j = k
            jd = kd
            k = revert(k, pf)
        end
        for l = 1:d
            F[jd+l] = s[l]
        end
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
