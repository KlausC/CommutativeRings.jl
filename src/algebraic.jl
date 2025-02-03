
import Base: *, /, inv, +, -, sqrt, cbrt, ^, literal_pow, iszero, zero, one, ==, hash
import Base: conj, real, imag, abs, copy

# construction
category_trait(::Type{<:AlgebraicNumber}) = FieldTrait
basetype(::Type{<:AlgebraicNumber}) = QQ{BigInt}

function AlgebraicNumber(p::UnivariatePolynomial{<:basetype(AlgebraicNumber)}, a = 0)
    ps = [first(x) for x in factor(p)]
    p, a = findbest(ps, a)
    AlgebraicNumber(p, a, NOCHECK)
end
function AlgebraicNumber(a::RingIntRatSc)
    Q = basetype(AlgebraicNumber)
    x = monom(Q[:x])
    qa = Q(a)
    AlgebraicNumber(x - qa, qa, NOCHECK)
end
function AlgebraicNumber(p::UnivariatePolynomial, a = 0)
    Q = basetype(AlgebraicNumber)
    AlgebraicNumber(Q[:x](p), a)
end
AlgebraicNumber(a::AlgebraicNumber) = a

Base.convert(::Type{T}, a::Union{Integer,Rational}) where T<:AlgebraicNumber = T(a)
Base.convert(::Type{T}, a::Ring) where T<:AlgebraicNumber = T(a)
Base.convert(::Type{T}, a::AlgebraicNumber) where T<:AlgebraicNumber = a

# promotion and conversion
promote_rule(::Type{<:AlgebraicNumber}, ::Type{<:QQ}) = AlgebraicNumber
promote_rule(::Type{<:AlgebraicNumber}, ::Type{<:ZZ}) = AlgebraicNumber
promote_rule(::Type{<:AlgebraicNumber}, ::Type{<:Integer}) = AlgebraicNumber
promote_rule(::Type{<:AlgebraicNumber}, ::Type{<:Rational}) = AlgebraicNumber

copy(a::AlgebraicNumber) = typeof(a)(poly(a), approx(a))
==(a::T, b::T) where T<:AlgebraicNumber = poly(a) == poly(b) && approx(a) == approx(b)
hash(a::AlgebraicNumber, x::UInt) = hash(poly(a), hash(approx(a), x))

function minimalpart(p::UnivariatePolynomial)
    f = factor(p)
    _, i = findmin(x -> deg(first(first(x))), f)
    first(f[i])
end

poly(a::AlgebraicNumber) = a.minpol
approx(a::AlgebraicNumber) = a.approx
deg(a::AlgebraicNumber) = deg(poly(a))
zero(::Type{T}) where T<:AlgebraicNumber =
    T(UnivariatePolynomial{basetype(T),:x}([0, 1]), 0)
one(::Type{T}) where T<:AlgebraicNumber =
    T(UnivariatePolynomial{basetype(T),:x}([-1, 1]), 1)
iszero(a::AlgebraicNumber) = deg(a) == 1 && iszero(poly(a)(0))
isone(a::AlgebraicNumber) = deg(a) == 1 && isone(poly(a)(0))
isunit(a::AlgebraicNumber) = !iszero(a)

function literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{2})
    p = poly(a)
    x = monom(typeof(p))
    q = compress(p(-x) * p, 2)
    if isodd(deg(p))
        q = -q
    end
    AlgebraicNumber(q, approx(a)^2)
end
literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{1}) = a
literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{3}) = pow(a, 3)
literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{-1}) = inv(a)
literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{-2}) = inv(a^2)

^(a::AlgebraicNumber, n::Integer) = pow(a, n)
function ^(a::AlgebraicNumber, q::Rational{<:Integer})
    n, d = numerator(q), denominator(q)
    if n == 1
        root(a, d)
    elseif n == -1
        inv(root(a, d))
    elseif n >= 0
        root(a^n, d)
    else
        root(inv(a^(-n)), d)
    end
end

function _pow(p::UnivariatePolynomial, m::Integer)
    x = monom(typeof(p))
    n = deg(p)
    C = zeros(basetype(p), n, n)
    for i = 1:n
        q = rem(x^(m + i - 1), p)
        b = q.first
        c = q.coeff
        for j = 1:length(c)
            C[j+b, i] = c[j]
        end
    end
    C
end
function pow(a::AlgebraicNumber, m::Integer)
    C = _pow(poly(a), m)
    x = monom(typeof(poly(a)))
    AlgebraicNumber(det(x * I - C), approx(a)^m)
end

function root(a::AlgebraicNumber, n::Integer)
    p = uncompress(poly(a), n)
    AlgebraicNumber(p, approx(a)^(1 // n))
end

sqrt(a::AlgebraicNumber) = ^(a, 1 // 2)
cbrt(a::AlgebraicNumber) = ^(a, 1 // 3)
conj(a::AlgebraicNumber) = AlgebraicNumber(poly(a), conj(approx(a)), NOCHECK)
real(a::AlgebraicNumber) = (a + conj(a)) / 2
imag(a::AlgebraicNumber) = (a - conj(a)) / 2
abs(a::AlgebraicNumber) =
    !isreal(approx(a)) ? sqrt(a * conj(a)) : real(approx(a)) >= 0 ? a : -a

function *(a::T, b::T) where T<:AlgebraicNumber
    if a == b
        literal_pow(^, a, Val(2))
    else
        pab = multiply(a, b)
        AlgebraicNumber(pab, approx(a) * approx(b))
    end
end

*(a::T, aa::Ring) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(poly(a), aa), approx(a) * value(aa))
*(aa::Ring, a::T) where T<:AlgebraicNumber = a * aa
*(a::T, aa::RingIntRatSc) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(poly(a), aa), approx(a) * value(aa))
*(aa::RingIntRatSc, a::T) where T<:AlgebraicNumber = a * aa

+(a::T, b::T) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(poly(a), poly(b), 1, 1), approx(a) + approx(b))
-(a::T, b::T) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(poly(a), poly(b), 1, -1), approx(a) - approx(b))
-(a::T) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(poly(a), poly(a), -1, 0), -approx(a))

function multiply(a::T, b::T) where T<:AlgebraicNumber
    ca = companion(poly(a))
    cb = companion(poly(b))
    characteristic_polynomial(kron(ca, cb))
end

function lincomb(a::T, b::T, aa, bb) where T<:UnivariatePolynomial
    if iszero(bb)
        lincomb(a, aa)
    elseif iszero(aa)
        lincomb(b, bb)
    else
        ca = companion(a)
        cb = companion(b)
        ea = I(deg(a)) * bb
        eb = I(deg(b)) * aa
        characteristic_polynomial(kron(ca, eb) + kron(ea, cb))
    end
end

function lincomb(p::T, aa) where T<:UnivariatePolynomial
    if isone(aa)
        p
    else
        q = copy(p)
        qq = q.coeff
        bb = aa
        n = length(qq)
        for i = n-1:-1:1
            qq[i] *= bb
            bb *= aa
        end
        q
    end
end

function inv(a::T) where T<:AlgebraicNumber
    p = poly(a)
    q = reverse(p)
    q /= LC(q)
    AlgebraicNumber(q, inv(approx(a)))
end

# find best of irreducible factors with respect to having a root close to `a`.
function findbest(ps::Vector, a)
    _, i = findmin(ps) do p
        dp = derive(p)
        abs(p(a) / dp(a))
    end
    p = ps[i]
    b = closeroot(p, big(value(a)))
    p, b
end

value(a::Number) = float(a)

import Polynomials: Polynomials, roots

# find root of `p`, which is closest to `a`.
function closeroot(p, a)
    dp = derive(p)
    epsa = eps(float(real(typeof(a))))
    epsb = abs(a) * sqrt(epsa)
    da = p(a) / dp(a)
    if abs(da) > epsa * abs(a) * 2^20
        pp = Polynomials.Polynomial(Float64.(value.(coeffs(p))))
        r = roots(pp)
        _, i = findmin(r) do x
            abs(a - x)
        end
        a = oftype(a, r[i])
        da = p(a) / dp(a)
    end
    i = 100
    while true
        a -= da
        i -= 1
        i = abs(da) < epsb ? min(1, i) : i
        i > 0 || break
        da = p(a) / dp(a)
    end
    a
end
