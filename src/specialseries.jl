module SpecialPowerSeries

using CommutativeRings
export B, E, podhammer, stirling1, stirling2, stirling1r, stirling2r
export Li, Ein, lin1p, lin1pe
export exp, expm1, log1p, sqrt1p, power1p
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

Return value of "polylogarithmic" function `Li` of order `n`.
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
    lin1p(z) = lin(1 + z) = -Ein(-log(1 + z))

Return "logarithmic integral" normalizing function.

We have:
 * `lin(z) = lin1p(z - 1)`
 * `li(z) = Ei(log(z))`
 * `li(z) = γ + log(|log(z)|) + lin(z)` for `z > 0`
"""
lin1p(z) = -Ein(-log1p(z))

"""
    lin1pe(u) = lin1p(expm1(u))

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

"""
    power1p(z, p) = (1 + z)^p
"""
function power1p(z::PowerSeries, p::QQ)
    s = one(z)
    a = s[0]
    for i = 1:p1(z)
        a = a * (p - i + 1) / i
        s += a * z^i
    end
    s
end
power1p(z::PowerSeries, p) = power1p(z, QQ(p))

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

function bernoulli_numbers!(b::Vector{T}, n::Integer) where T<:Rational{BigInt}
    isodd(n) && return b
    n0 = n ÷ 2
    m0 = length(b)
    m0 > n0 && return b
    n0 += 50 ÷ (m0 + 10)
    resize!(b, n0)
    for m = m0+1:n0
        s = -one(T) // (2m + 1) + 1 // 2
        for k = 1:m-1
            s -= binomial(big(2m), big(2k)) // (2m - 2k + 1) * b[k]
        end
        b[m] = s
    end
    return b
end

function bernoulli_number(k::Integer)
    T = eltype(BL)
    k == 0 && return one(T)
    k == 1 && return -one(T) / 2
    isodd(k) && return zero(T)
    b = bernoulli_numbers!(BL, k)
    b[k÷2]
end

# global store for Euler numbers
const EL = BigInt[]

function euler_numbers!(b::Vector{T}, m::Integer) where T
    m0 = length(b)
    m0 > m && return b
    m += 50 ÷ (m0 + 10)
    resize!(b, m)
    m0 == 0 && (b[1] = 1)
    for n = max(m0, 1):m-1
        s = zero(T)
        for k = 1:n
            s -= binomial(big(2n), big(2k - 2)) * b[k]
        end
        b[n+1] = s
    end
    b
end

function euler_number(k::Integer)
    isodd(k) && return zero(eltype(EL))
    b = euler_numbers!(EL, (k + 2) ÷ 2)
    b[(k+2)÷2]
end

"""
    B(n), B(n, x)

Bernoulli-number and Bernoulli-polynomial
"""
function B(m, x)
    sum(bernoulli_euler_kernel(m, x, n) / (n + 1) for n = big(0):m)
end

"""
    E(n), E(n, x)

Euler-number and Euler-polynomial
"""
function E(m, x)
    sum(bernoulli_euler_kernel(m, x, n) / 2^n for n = big(0):m)
end

function bernoulli_euler_kernel(m, x, n)
    sum((-1)^k * binomial(n, k) * (x + k)^m for k = 0:n)
end

"""
    Podhammer(x, n::Integer)

Podhammer symbol.

Decreasing product: `podhammer(x, 3)  = x * (x-1) * (x-2)`

Increasing product: `podhammer(x, -3) = x * (x+1) * (x+2)`.
"""
function podhammer(x, n)
    n1 = n + 1
    if n1 < 0
        x = x - n1
    end
    n = abs(n)
    prod(x - k for k = 0:n-1; init = one(x))
end

"""
    stirling1(n, k)

Stirling numbers of the first kind. See also `stirling1r`.
"""
function stirling1(n::T, k::T) where T<:Integer
    us = _stirling1(n, k)
    us < 0 && throw(OverflowError("ustirling($n, $k) overflows"))
    iseven(n - k) ? us : -us
end
function _stirling1(n::T, k::T) where T<:Integer
    if k == n && n >= 0
        one(T)
    elseif k <= 0 || k > n
        zero(T)
    elseif k == 1
        factorial(n - 1)
    elseif k == n - 1
        binomial(n, 2)
    elseif k == n - 2
        binomial(n, 3) * (3n - 1) ÷ 4
    elseif k == n - 3
        binomial(n, 2) * binomial(n, 4)
    else
        if 2k <= n
            b = ones(T, k)
            for j = 1:n-k
                b[1] *= j
                for i = 2:k
                    b[i] = b[i] * (j + i - 1) + b[i-1]
                end
            end
            b[k]
        else
            nk = n - k
            b = zeros(T, nk)
            b[1] = 1
            for i = 2:nk
                b[i] = b[i-1] * i
            end
            for j = 1:k-1
                b[1] += (j + 1)
                for i = 2:nk
                    b[i] += b[i-1] * (i + j)
                end
            end
            b[nk]
        end
    end
end
stirling1(n, k) = stirling1(promote(n, k)...)
"""
    stirling1r(n, k)

Unsigned Stirling numbers of first kind. `stirling1r(n, k) = (-1)^(n-k) * stirling1(n, k)`
"""
stirling1r(n, k) = _stirling1(promote(n, k)...)

"""
    stirling2(n, k)

Stirling numbers of the second kind. See also `stirling2r`.
"""
function _stirling2(n::T, k::T) where T<:Integer
    if k == n && n >= 0
        one(T)
    elseif k <= 0 || k > n
        zero(T)
    elseif k == 1
        one(T)
    elseif k == n - 1
        binomial(n, 2)
    elseif k == 2
        2^(n - 1) - 1
    else
        sum((-1)^i * i^n * binomial(k, i) for i = 1:k) * (-1)^k ÷ factorial(k)
    end
end
stirling2(n, k) = _stirling2(promote(n, k)...)
"""
    stirling2r(n, k)

Signed Stirling numbers of second kind. `striling2r(n, k) = (-1)^(n-k) * stirling2(n, k)`.
"""
function stirling2r(n, k)
    us = _stirling2(promote(n, k)...)
    iseven(n - k) ? us : -us
end

end # module
