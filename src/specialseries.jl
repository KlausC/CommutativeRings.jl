module SpecialPowerSeries

using CommutativeRings
export bernoulli_number, euler_number
export Li, Ein, lin1p, lin1pe
export exp, expm1, log1p, sqrt1p
export sin, cos, tan, cot, csc, sec, asin, atan, ver
export sinh, cosh, tanh, coth, csch, sech, asinh, atanh

import Base: exp, expm1, log1p
import Base: sin, cos, tan, cot, csc, sec, asin, atan
import Base: sinh, cosh, tanh, coth, csch, sech, asinh, atanh

p1(z) = big(precision(typeof(z)) + 1)
p2(z) = big((precision(typeof(z)) + 1) ÷ 2)

B(k::Integer) = bernoulli_number(k)
E(k::Integer) = euler_number(k)
fac(k::Integer) = factorial(big(k))

"""
    Li(z, n)

Return value of "polylogarithmic" function`Li` of order `n`.
"""
Li(z::PowerSeries, n::Integer) = sum(z^k / k^n for k ∈ 1:p1(z))

"""
    Ein(z)

Return "exponential integral" normalizing function.

We have also
 * `Ei(z) = γ + log(|z|) - Ein(-z)` for `z != 0`
 * `E_1(z) = -γ -log(z) + Ein(z)` for `|arg(z)| < π`
"""
Ein(z) = sum(-(-1)^k * z^k / (k * fac(k)) for k ∈ 1:p1(z))

"""
    lin1p(z) = lin(1 + z) = Ein(-log(1 + z))

Return "logarithmic integral" normalizing function.

We have:
 * `lin(z) = lin1p(z - 1)`
 * `li(z) = Ei(log(z))`
 * `li(z) = γ + log(|log(z)|) + lin(z)` for `z > 0`
"""
lin1p(z) = -Ein(-log1p(z))

"""
    lin1pe(u) = lin1p(expm112(u))

Return "logarithmic integral" variant.

Faster converging series, if applied to `log(z)` devoted to Ramanujan.

 * lin1pe(log1p(z)) == lin1p(z)
"""
lin1pe(z) = exp(z / 2) * Ein2(z)
hsum(n::Integer) = sum(1 // k for k = 1:2:n)
Ein2(z) = sum(-(-1)^n * z^n / (fac(n) * 2^(n - 1)) * hsum(n) for n = 1:p1(z))

exp(z) = sum(z^k / fac(k) for k = 0:p1(z))

#exp(z) - 1
expm1(z) = sum(z^k / fac(k) for k = 1:p1(z))

# log(1 + z)
log1p(z) = sum(-(-z)^k / k for k = 1:p1(z))

"""
    sqrt1p(z) = sqrt(1 + z)
"""
sqrt1p(z) = sum(-(-1)^k * binomial(2k, k) * (z / 4)^k / (2k - 1) for k = 0:p1(z))

sin(z) = sum((-1)^k * z^(2k + 1) / fac(2k + 1) for k ∈ 0:p2(z))
sinh(z) = sum(z^(2k + 1) / fac(2k + 1) for k ∈ 0:p2(z))

cos(z) = sum((-1)^k * z^2k / fac(2k) for k ∈ 0:p2(z))
cosh(z) = sum(z^2k / fac(2k) for k ∈ 0:p2(z))

tan(z) = sum(-(-1)^k * (2^2k - 1) * 2^2k * B(2k) * z^(2k - 1) / fac(2k) for k = 1:p2(z))
tanh(z) = sum((2^(2k) - 1) * 2^2k * B(2k) * z^(2k - 1) / fac(2k) for k = 1:p2(z))

# cot(z) - 1 / z
cot(z) = sum((-1)^k * 2^2k * B(2k) / fac(2k) * z^(2k - 1) for k ∈ 0:p2(z))
coth(z) = sum(2^2k * B(2k) / fac(2k) * z^(2k - 1) for k ∈ 0:p2(z))

# csc(z) - 1 / z
csc(z) = sum(-(-1)^k * (2^2k - 2) * B(2k) * z^(2k - 1) / fac(2k) for k ∈ 0:p2(z))
csch(z) = sum(-(2^2k - 2) * B(2k) * z^(2k - 1) / fac(2k) for k ∈ 0:p2(z))

sec(z) = sum((-1)^k * E(2k) * z^2k / fac(2k) for k ∈ 0:p2(z))
sech(z) = sum(E(2k) * z^2k / fac(2k) for k = 0:p2(z))

"""
    ver(z) = 1 - cos(z)

Return the versine of `z`
"""
ver(z) = sum(-(-1)^k * z^2k / fac(2k) for k = 1:p2(z)+1)

asin(z) = sum(fac(2k) * z * z^2k / (2^2k * fac(k)^2 * (2k + 1)) for k ∈ 0:p2(z))
asinh(z) = sum((-1)^k * fac(2k) * z * z^2k / (2^2k * fac(k)^2 * (2k + 1)) for k ∈ 0:p2(z))

atan(z) = sum((-1)^k * z^(2k + 1) / (2k + 1) for k ∈ 0:p2(z))
atanh(z) = sum(z^(2k + 1) / (2k + 1) for k ∈ 0:p2(z))

# global store for Bernoulli numbers
const BL = Rational{BigInt}[]

function bernoulli_numbers!(b::Vector{Rational{BigInt}}, n::Integer)
    m0 = length(b)
    m0 > n && return b
    n += 20
    resize!(b, max(2, n + 1))
    b[1] = 1
    b[2] = -1 // 2
    for m = max(2, m0):n
        s = zero(b[1])
        for k = 0:m-1
            s -= binomial(big(m), big(k)) // (m - k + 1) * b[k+1]
        end
        b[m+1] = s
    end
    return b
end

function bernoulli_number(k::Integer)
    b = bernoulli_numbers!(BL, k)
    b[k+1]
end

# global store for Euler numbers
const EL = BigInt[]

function euler_numbers!(b::Vector{T}, m::Integer) where T
    m0 = length(b)
    m0 > m && return b
    m += 20
    resize!(b, m + 1)
    b[1] = 1
    for n = max(m0, 1):m
        n2 = 2n
        s = zero(T)
        g = -1
        for l = 1:n2
            t = zero(T)
            for q = 0:l
                t += binomial(big(l), big(q)) * big(2q - l)^n2
            end
            s += t * binomial(big(n2), big(l)) // (big(2)^l * (l + 1)) * g
            g = -g
        end
        b[n+1] = s * (n2 + 1)
    end
    b
end

function euler_number(k::Integer)
    isodd(k) && return zero(eltype(EL))
    b = euler_numbers!(EL, (k + 2) ÷ 2)
    b[(k+2)÷2]
end

end # module
