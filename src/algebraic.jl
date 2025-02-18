
import Base: *, /, inv, +, -, sqrt, ^, literal_pow, iszero, zero, one, ==, isapprox, hash
import Base: conj, real, imag, abs, copy, isreal

# construction
basetype(::Type{<:AlgebraicNumber}) = QQ{BigInt}
category_trait(::Type{A}) where A<:AlgebraicNumber = category_trait(basetype(A))

function AlgebraicNumber(
    p::UnivariatePolynomial{<:basetype(AlgebraicNumber)},
    a::Number = -Inf,
    ::Val = Val(:check),
)
    ps = [first(x) / LC(first(x)) for x in sff(p)]
    p, a, r, id = findbest(ps, a)
    AlgebraicNumber(p, r, id, a, NOCHECK)
end
function AlgebraicNumber(
    p::UnivariatePolynomial{<:basetype(AlgebraicNumber)},
    a::Number,
    ::Val{:irreducible},
)
    r = cr_roots(p)
    a, id = closeroot(p, big(value(a)), r)
    AlgebraicNumber(p, r, id, a, NOCHECK)
end
function AlgebraicNumber(a::Union{Integer,Rational{<:Integer},ZZ,QQ})
    Q = basetype(AlgebraicNumber)
    x = monom(Q[:x])
    qa = Q(a)
    AlgebraicNumber(x - qa, [Float64(qa)], 1, qa, NOCHECK)
end
function AlgebraicNumber(a::Complex)
    if isreal(a)
        return AlgebraicNumber(real(a))
    end
    Q = basetype(AlgebraicNumber)
    x = monom(Q[:x])
    ra = Q(real(a))
    ia = Q(imag(a))
    ca = ComplexF64(a)
    id = 1
    if ia >= 0
        id = 2
        ca = conj(ca)
    end
    AlgebraicNumber(x^2 - 2*ra * x + ia^2 + ra^2, [ca, conj(ca)], id, a, NOCHECK)
end

function AlgebraicNumber(p::UnivariatePolynomial, a = -Inf)
    Q = basetype(AlgebraicNumber)
    AlgebraicNumber(Q[:x](p), a)
end
AlgebraicNumber(a::AlgebraicNumber) = a
function AlgebraicNumber(b::NumberField, ab = approx(b))
    AlgebraicNumber(field_polynomial(b), ab)
end

# promotion and conversion
Base.convert(::Type{T}, a::Union{Integer,Rational,Complex}) where T<:AlgebraicNumber = T(a)
Base.convert(::Type{T}, a::Ring) where T<:AlgebraicNumber = T(a)
Base.convert(::Type{T}, a::AlgebraicNumber) where T<:AlgebraicNumber = a

promote_rule(::Type{<:A}, ::Type{<:QQ}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:ZZ}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:Integer}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:Rational}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:Complex}) where A<:AlgebraicNumber = A

copy(a::AlgebraicNumber) = typeof(a)(minimal_polynomial(a), approx(a))

function Base.show(io::IO, a::AlgebraicNumber)
    aa = approx(a)
    print(io, "AlgebraicNumber(", string(minimal_polynomial(a)), ", ", a.rootid, ", ")
    print(io, isreal(a) ? Float64(aa) : ComplexF64(aa), ")")
end

function ==(a::T, b::T) where T<:AlgebraicNumber
    ma = minimal_polynomial(a)
    mb = minimal_polynomial(b)
    ma == mb && (deg(ma) <= 1 || a.rootid == b.rootid)
end

function Base.hash(a::AlgebraicNumber, x::UInt)
    p = minimal_polynomial(a)
    if deg(p) <= 1
        hash(-p[0], x)
    else
        hash(p, hash(a.rootid, x))
    end
end

minimal_polynomial(a::AlgebraicNumber) = a.minpol
approx(a::AlgebraicNumber) = a.approx
deg(a::AlgebraicNumber) = deg(minimal_polynomial(a))
Base.zero(::Type{T}) where T<:AlgebraicNumber =
    T(UnivariatePolynomial{basetype(T),:x}([0, 1]), 0)
Base.one(::Type{T}) where T<:AlgebraicNumber =
    T(UnivariatePolynomial{basetype(T),:x}([-1, 1]), 1)
Base.iszero(a::AlgebraicNumber) = deg(a) == 1 && minimal_polynomial(a).first == 1
isone(a::AlgebraicNumber) = deg(a) == 1 && isone(-minimal_polynomial(a)[0])
isunit(a::AlgebraicNumber) = !iszero(a)

approx(a::Union{Integer,Rational,ZZ,QQ}) = float(value(a))

function literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{2})
    p = minimal_polynomial(a)
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
    if d == 1
        a^n
    elseif n == 1
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
        for j in axes(c, 1)
            C[j+b, i] = c[j]
        end
    end
    C
end
function pow(a::A, m::Integer) where A<:AlgebraicNumber
    m == 0 ? one(A) : m == 1 ? a : evaluate(monom((basetype(A)[:x]), m), a)
end

function evaluate(p::UnivariatePolynomial, a::A) where A<:AlgebraicNumber
    A(evaluate(p, monom(NF(a))), p(approx(a)))
end

function root(a::AlgebraicNumber, n::Integer)
    p = uncompress(minimal_polynomial(a), n)
    AlgebraicNumber(p, approx(a)^(1 // n))
end

# The imaginary constant a algebraic number
IM() = AlgebraicNumber(monom(QQ{Int}[:x], 2) + 1, im)

sqrt(a::AlgebraicNumber) = ^(a, 1 // 2)
# cbrt(a::AlgebraicNumber) = ^(a, 1 // 3) # intentionally not defined - alike Complex.
isreal(a::AlgebraicNumber) = isreal(approx(a))
real(a::AlgebraicNumber) = isreal(a) ? a : (a + conj(a)) / 2
imag(a::AlgebraicNumber) = isreal(a) ? zero(a) : (conj(a) - a) * IM() / 2
abs(a::AlgebraicNumber) = !isreal(a) ? sqrt(a * conj(a)) : real(approx(a)) >= 0 ? a : -a

function *(a::T, b::T) where T<:AlgebraicNumber
    if a == b
        literal_pow(^, a, Val(2))
    elseif iszero(a) || iszero(b)
        zero(T)
    else
        pab = multiply(a, b)
        AlgebraicNumber(pab, approx(a) * approx(b))
    end
end

*(a::T, aa::RingNumber) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(minimal_polynomial(a), aa), approx(a) * value(aa))
*(aa::RingNumber, a::T) where T<:AlgebraicNumber = a * aa
*(p::P, a::R) where {R<:AlgebraicNumber,P<:UnivariatePolynomial{R}} = P(coeffs(p) .* a)
*(a::R, p::P) where {R<:AlgebraicNumber,P<:UnivariatePolynomial{R}} = P(coeffs(p) .* a)

/(aa::T, a::T) where T<:AlgebraicNumber = inv(a) * aa
/(aa::RingNumber, a::T) where T<:AlgebraicNumber = inv(a) * aa
/(aa::T, a::RingNumber) where T<:AlgebraicNumber = aa * inv(basetype(T)(a))

+(a::T, b::T) where T<:AlgebraicNumber = AlgebraicNumber(
    lincomb(minimal_polynomial(a), minimal_polynomial(b), 1, 1),
    approx(a) + approx(b),
)
-(a::T, b::T) where T<:AlgebraicNumber = AlgebraicNumber(
    lincomb(minimal_polynomial(a), minimal_polynomial(b), 1, -1),
    approx(a) - approx(b),
)
-(a::T) where T<:AlgebraicNumber = AlgebraicNumber(
    lincomb(minimal_polynomial(a), minimal_polynomial(a), -1, 0),
    -approx(a),
)

function multiply(a::T, b::T) where T<:AlgebraicNumber
    ca = companion(minimal_polynomial(a))
    cb = companion(minimal_polynomial(b))
    characteristic_polynomial(kron(ca, cb))
end

function lincomb(a::T, b::T, aa, bb) where T<:UnivariatePolynomial
    if iszero(bb)
        lincomb(a, aa)
    elseif iszero(aa)
        lincomb(b, bb)
    elseif a == b
        ca = companion(a)
        ea = I(deg(a))
        characteristic_polynomial(kron(ca, ea * aa) + kron(ea * bb, ca))
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
    p = minimal_polynomial(a)
    q = reverse(p)
    q /= LC(q)
    AlgebraicNumber(q, inv(approx(a)))
end

# find best of irreducible factors with respect to having a root close to `a`.
function findbest(ps::AbstractVector{<:UnivariatePolynomial}, a::Number)
    p = bestpoly(ps, a)
    if isreducible(p)
        pss = [first(s) for s in factor(p)]
        p = bestpoly(pss, a)
    end
    r = cr_roots(p)
    b, id = closeroot(p, big(value(a)), r)
    p, b, r, id
end

function bestpoly(ps::AbstractVector{<:UnivariatePolynomial}, a::Number)
    if length(ps) > 1
        _, i = findmin(ps) do p
            pa = abs(p(a))
            dpa = abs(derive(p)(a))
            dpa <= pa ? pa : pa / dpa
        end
    else
        i = 1
    end
    ps[i]
end


value(a::Number) = float(a)

# find root of `p`, which is closest to `a`.
function closeroot(p::UnivariatePolynomial, a::Number, r::AbstractVector{<:Number})
    p = primpart(p) # converts to ZZ[:x] - faster than QQ[:x]

    dp = derive(p)
    id, a = nextroot(a, r)
    da = p(a) / dp(a)
    epsb = abs(a) * sqrt(eps(real(typeof(a))))
    i = 100
    for _ = 1:i
        a -= da
        i -= 1
        i = abs(da) < epsb ? min(1, i) : i
        i > 0 || return a, id
        da = p(a) / dp(a)
    end
    throw(NumericalError("polynomial root finding did not converge"))
end

struct NumericalError <: Exception
    text::AbstractString
end

function cr_roots(p::UnivariatePolynomial)
    A = companion(Float64, p)
    roots = LinearAlgebra.eigvals(A; permute = false, scale = false)
    map(roots) do x
        e = sqrt(eps())
        abs(real(x)) < e * abs(imag(x)) ? Complex(0, imag(x)) : x
    end
end

function nextroot(a, r::AbstractVector)
    _, i = findmin(r) do v
        if isfinite(a)
            abs(a - v)
        elseif a == Inf
            -real(v)
        else
            real(v)
        end
    end
    i, Complex{float(real(typeof(a)))}(r[i]), r
end

function Base.conj(a::AlgebraicNumber)
    if isreal(a)
        a
    else
        ap, id = closeroot(minimal_polynomial(a), conj(approx(a)), a.roots)
        AlgebraicNumber(minimal_polynomial(a), a.roots, id, ap, NOCHECK)
    end
end

function Base.conj(a::AlgebraicNumber, n::Integer)
    m = deg(a)
    n = mod1(n, m)
    n == a.rootid && return a
    ap, id = closeroot(minimal_polynomial(a), a.roots[n], a.roots)
    AlgebraicNumber(minimal_polynomial(a), a.roots, id, ap, NOCHECK)
end

"""
    field_polynomial(α::AlgebraicNumber, b)

Calculate the field polynomial over the field Q(α) for a field element β, which
is represented as a polynomial of `α` of degree <= degree of α.

Implemented In numberfield realm.
"""
function field_polynomial end

"""
    field_polynomial(α, b, Val(true))

This algorithm is not efficient to calculate the minimal polynomial of `β`, because
the number of terms in the elementary symmetric functions explodes with the degree of `α`.

Try the methods of `NumberField` for these calculations using the `companion` methods.
"""
function field_polynomial(
    a::A,
    b::B,
    ::Val{true},
) where {A<:AlgebraicNumber,B<:UnivariatePolynomial}
    n = deg(a)
    p = minimal_polynomial(a)
    QX = typeof(p)
    Q = basetype(QX)
    # set up a multivariate polynomial with variables a(1), ... a(n)
    vars = [[Symbol("α(", k, ")")] for k = 1:n]
    M = Q[vars...]
    g = generators(M)
    sigmas = [b(g[k]) for k = 1:n]
    # PX = M[:X]
    # X = monom(PX)
    # the field polynomial in terms of the a(i)
    # fp = prod(X - sigma(i) for i = 1:n)
    # the coefficients of fp are the elementary symmetric functions of the a(i)
    # as they are symmetric in a(i), they can be expressed by the symmetric e(i)
    # which are essentially the coefficients of the minimal polynomial of α.
    ce = Vector{Q}(undef, n + 1)
    ce[n+1] = one(Q)
    for i = 1:n
        cai = elementary_symmetric(M, i)(sigmas...)
        ce[n-i+1] = newton_symmetric(cai)(((-1)^j * p[n-j] for j = 1:n)...) * (-1)^i
    end
    QX(ce)
end

"""
    cispi(r::QQ)

Return the algebraic number at `exp(pi * r * im)`.
"""
Base.cispi(q::Q) where Q<:QQ = cispi(Q, value(q))
function Base.cispi(Q::Type{<:QQ}, r::Rational{<:Integer})
    r = mod(r + 1, 2) - 1
    r //= 2
    num = numerator(r)
    den = denominator(r)
    p = cyclotomic(big(Q)[:x], den)
    e = cispi(1 / den)
    pow(AlgebraicNumber(p, e, Val(:irreducible)), num)
end

function Base.sincospi(q::QQ)
    d = cispi(q)
    N = NF(d)
    e = monom(N)
    a = e
    b = inv(e)
    c = (a + b) / 2
    s = ((a - b) / 2)^2
    fs, fc = sincospi(big(value(q)))
    as = sqrt(AlgebraicNumber(-s, fs^2))
    ac = AlgebraicNumber(c, fc)
    as, ac
end
function Base.sinpi(q::QQ)
    d = cispi(q)
    N = NF(d)
    a = monom(N)
    b = inv(a)
    s = (a - b) / 2
    fs = sinpi(big(value(q))) * im
    as = AlgebraicNumber(s, fs) / IM()
    as
end
function Base.cospi(q::QQ)
    d = cispi(q)
    N = NF(d)
    a = monom(N)
    b = inv(a)
    c = (a + b) / 2
    fc = cospi(big(value(q)))
    ac = AlgebraicNumber(c, fc)
    ac
end

"""
    rationalconst(expr)

Return the value of a rational constant or a rational function of rational constants
if that can be expressed as `Rational`. Otherwise return `nothing`.
"""
rationalconst(x::Integer) = big(x)
rationalconst(::Any) = nothing

function rationalconst(expr::Expr)
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        fun = fun == :(/) ? :(//) : fun
        if fun == :(^)
            p = rationalconst(args[2])
            isnothing(p) && return p
            q = rationalconst(args[3])
            isnothing(q) && return q
            denominator(q) != 1 && return nothing
            return p^numerator(q)
        elseif fun == :inv
            p = rationalconst(args[2])
            isnothing(p) && return p
            return inv(p)
        end
        if fun ∉ (:(+), :(-), :(*), :(//), :(inv), (:sqrt))
            return false
        end
        n = length(args)
        eargs = similar(args)
        eargs[1] = fun
        for j = 2:n
            earg = rationalconst(args[j])
            isnothing(earg) && return nothing
            eargs[j] = earg
        end
        eval(Expr(head, eargs...))
    else
        nothing
    end
end

"""
    isalgebraic(expr)

Return true iff the expression describes an `AlgebraicNumber`.
"""

isalgebraic(::AlgebraicNumber) = true
isalgebraic(::Union{Rational,Integer}) = true
isalgebraic(::Any) = false

function isalgebraic(expr::Expr)
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        fun = fun == :(/) ? :(//) : fun
        if fun == :(^)
            isalgebraic(args[2]) || return false
            q = rationalconst(args[3])
            return !isnothing(q)
        elseif fun ∉ (:(+), :(-), :(*), :(//), :inv, :sqrt)
            return false
        end
        n = length(args)
        for j = 2:n
            isalgebraic(args[j]) || return false
        end
        return true
    else
        return false
    end
end

function AlgebraicNumber(expr::Expr)
    isalgebraic(expr) || throw(ArgumentError("expression is not an algebraic number"))
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        if fun == :(^)
            a = AlgebraicNumber(args[2])
            q = rationalconst(args[3])
            return a^q
        elseif fun ∈ (:(+), :(-), :(*), :(//), :(/), :inv, :sqrt)
            n = length(args)
            eargs = Vector{Any}(undef, n - 1)
            for j = 2:n
                eargs[j-1] = AlgebraicNumber(args[j])
            end
            return evaluate(Val(fun), eargs)
        end
        throw(ArgumentError("unknown function $fun"))
    else
        throw(ArgumentError("no call, but $head"))
    end
end

evaluate(::Val{:(+)}, args) = +(args...)
evaluate(::Val{:(-)}, args) = -(args...)
evaluate(::Val{:(*)}, args) = *(args...)
evaluate(::Val{:(/)}, args) = //(args...)
evaluate(::Val{:(//)}, args) = //(args...)
evaluate(::Val{:(inv)}, args) = inv(args...)
evaluate(::Val{:(sqrt)}, args) = sqrt(args...)
