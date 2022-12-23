module FastPolyMul

using CommutativeRings
using CommutativeRings: ilog2
using Base.GMP.MPZ

export polymult

# The first approach tries to expolit the fast integer multiplication
# for univariate polynomials.
# The effort for data transformations seems to outweigth the advantages of the fast GMP
# implementation.

function polymult(p1::P, p2::P) where P<:UnivariatePolynomial{<:ZZ}
    s1 = value.(p1.coeff)
    s2 = value.(p2.coeff)
    est = maximum(mult_estimate(s1, s2))
    bits = CommutativeRings.ilog2(est) + 2
    twop = one(eltype(s1)) << (bits + 1)
    for i in axes(s1, 1)
        if s1[i] < 0
            s1[i] += twop
        end
    end
    for i in axes(s2, 1)
        if s2[i] < 0
            s2[i] += twop
        end
    end
    est = maximum(mult_estimate(s1, s2))
    bits = CommutativeRings.ilog2(est) + 2
    i1 = evalpolyshift(s1, bits)
    i2 = evalpolyshift(s2, bits)
    i3 = i1 * i2
    s3 = splitpolyshift(i3, bits)
    for i in axes(s3, 1)
        if s3[i] >= twop
            s3[i] -= twop
        end
    end
    p3 = P(s3)
    p3, s3, i3
end

function mult_estimate(a::V, b::V) where V<:AbstractVector{<:Integer}
    m = length(a)
    n = length(b)
    U = (signed(eltype(V)))
    m * n == 0 && return U[]
    sa = abs2(a[1])
    sb = abs2(b[1])
    v = isqrt(sa * sb) + 1
    #println("k = 1, sa = $sa, sb = $sb")
    for k = 2:m+n-1
        if k <= m
            sa += abs2(a[k])
        end
        if k - n > 0
            sa -= abs2(a[k-n])
        end
        if k <= n
            sb += abs2(b[k])
        end
        if k > m
            sb -= abs2(b[k-m])
        end
        #println("k = $k, sa = $sa, sb = $sb")
        vv = isqrt(sa * sb) + 1
        if vv > v
            v = vv
        end
    end
    v
end

function evalpolyshift(a::AbstractVector{<:Integer}, ex::Integer)
    n = length(a)
    n == 0 && return zero(BigInt)
    s = BigInt(; nbits = n * ex)
    Base.GMP.MPZ.add_ui!(s, unsigned(a[n]))
    for k = n-1:-1:1
        Base.GMP.MPZ.mul_2exp!(s, unsigned(ex))
        Base.GMP.MPZ.add_ui!(s, unsigned(a[k]))
        # s = s << ex + a[k]
    end
    s
end

function splitpolyshift(a::BigInt, bits::Int)
    T = Int
    twop = one(T) << bits
    mask = twop - 1
    len = (ilog2(a) - 1) ÷ bits + 2
    s = Vector{T}(undef, len)
    for i = 1:len
        s[i] = rem(a, T) & mask
        Base.GMP.MPZ.fdiv_q_2exp!(a, a, unsigned(bits))
    end
    s
end

end #module

module FastPolyKaratsuba

using CommutativeRings
using CommutativeRings: multiply

# First implementation of Karatsuba's algorithm. TAoCP 4.3.3

export polymult

THRESHOLD1 = 100
THRESHOLD2 = 10000

function polymult(u::P, v::P) where P<:UnivariatePolynomial{<:Ring}
    # println("polymult($u, $v)")
    du = deg(u) - ord(u)
    dv = deg(v) - ord(v)
    if du * dv <= THRESHOLD2 || min(du, dv) <= THRESHOLD1
        return multiply(u, v, du + dv + 1)
    end
    x(k) = monom(P, k)

    mu = du ÷ 2
    mv = dv ÷ 2
    u1, u0 = split(u / x(ord(u)), mu)
    v1, v0 = split(v / x(ord(v)), mv)
    mu = du - deg(u1)
    mv = dv - deg(v1)
    k0 = mu ÷ 2
    l0 = mv ÷ 2
    k1 = mu - l0
    l1 = mv - k0
    K = min(k0, k1)
    L = min(l0, l1)
    k0, k1 = k0 - K, k1 - K
    l0, l1 = l0 - L, l1 - L
    p11 = polymult(u1, v1) * (x(mu + mv) + x(k1 + l1 + K + L))
    p01 = polymult(u1 * x(k1) - u0 * x(k0), v0 * x(l0) - v1 * x(l1)) * x(K + L)
    p00 = polymult(u0, v0) * (x(k0 + l0 + K + L) + 1)
    (p11  + p00  + p01) * x(ord(u) + ord(v))
end

function split(p::P, m::Integer) where P<:UnivariatePolynomial
    xm = monom(P, m)
    q, r = divrem(p, xm)
    q = q * monom(P, -ord(q))
    q, r
end

end # module
