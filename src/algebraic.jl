
import Base: *, /, inv, +, -, sqrt, ^, literal_pow, iszero, zero, one, ==, isapprox, hash
import Base: conj, real, imag, abs, copy, isreal, cispi, cospi, sinpi, tanpi
import Base.MathConstants: φ

# construction
basetype(::Type{<:AlgebraicNumber}) = QQ{ZZZ}
category_trait(::Type{A}) where A<:AlgebraicNumber = category_trait(basetype(A))

function AlgebraicNumber(
    p::UnivariatePolynomial{<:basetype(AlgebraicNumber)},
    a::Number = -Inf,
    ::Val = Val(:check),
)
    iszero(denominator(p[0])) && deg(p) == 1 && return AlgebraicNumber(Inf)
    isnan(a) && return AlgebraicNumber(NaN)
    ps = [first(x) / LC(first(x)) for x in sff(p)] # squarefree and monic
    p, a, r, id = findbest(ps, a)
    AlgebraicNumber(p, r, id, a, NOCHECK)
end
function AlgebraicNumber(
    p::UnivariatePolynomial{<:basetype(AlgebraicNumber)},
    a::Number,
    ::Val{:irreducible},
)
    r = cr_roots(p)
    a, id = closeroot(p, big(fvalue(a)), r)
    AlgebraicNumber(p, r, id, a, NOCHECK)
end
function AlgebraicNumber(a::Union{Integer,Rational{<:Integer},ZI,QQ})
    Q = basetype(AlgebraicNumber)
    x = monom(Q[:x])
    qa = Q(a)
    AlgebraicNumber(x - qa, [Float64(qa)], 1, qa, NOCHECK)
end

SMALL_INT = 1000
function AlgebraicNumber(a::AbstractFloat)
    isinteger(a) && return AlgebraicNumber(Integer(a))
    b = rationalize(a)
    bn = abs(numerator(b))
    bd = denominator(b)
    if !(bn < SMALL_INT && bd < SMALL_INT)
        R = typeof(b)
        throw(InexactError(R.name.name, R, a))
    end
    AlgebraicNumber(b)
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
    AlgebraicNumber(x^2 - 2 * ra * x + ia^2 + ra^2, [ca, conj(ca)], id, a, NOCHECK)
end
function AlgebraicNumber(a::Complex{<:AbstractFloat})
    r, i = reim(a)
    if iszero(i)
        AlgebraicNumber(r)
    else
        AlgebraicNumber(r) + AlgebraicNumber(i) * AlgebraicNumber(im)
    end
end
function AlgebraicNumber(s::Symbol)
    n = eval(s)
    n in (im, Base.MathConstants.φ) || throw(ArgumentError("symbol `$s` not supported"))
    AlgebraicNumber(n)
end
# note: `φ`` is typed `\varphi`
function AlgebraicNumber(::typeof(Base.MathConstants.φ))
    AlgebraicNumber(:((sqrt(5) + 1) / 2))
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
promote_rule(::Type{<:A}, ::Type{<:ZI}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:Integer}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:Rational}) where A<:AlgebraicNumber = A
promote_rule(::Type{<:A}, ::Type{<:AbstractFloat}) where A<:AlgebraicNumber = A
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
function approx(a::AlgebraicNumber, id::Integer)
    fap = a.roots[id]
    closeroot(minimal_polynomial(a), big(fap), a.roots)[1]
end
Base.zero(::Type{T}) where T<:AlgebraicNumber =
    T(UnivariatePolynomial{basetype(T),:x}([0, 1]), 0)
Base.one(::Type{T}) where T<:AlgebraicNumber =
    T(UnivariatePolynomial{basetype(T),:x}([-1, 1]), 1)
Base.iszero(a::AlgebraicNumber) = deg(a) == 1 && minimal_polynomial(a).first == 1
isone(a::AlgebraicNumber) = deg(a) == 1 && isone(-minimal_polynomial(a)[0])
isunit(a::AlgebraicNumber) = !iszero(a)

approx(a::Union{Integer,Rational,ZI,QQ}) = float(fvalue(a))

@inline function literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{2})
    p = minimal_polynomial(a)
    x = monom(typeof(p))
    q = compress(p(-x) * p, 2)
    if isodd(deg(p))
        q = -q
    end
    AlgebraicNumber(q, approx(a)^2)
end
@inline literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{1}) = a
@inline literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{3}) = pow(a, 3)
@inline literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{-1}) = inv(a)
@inline literal_pow(::typeof(^), a::AlgebraicNumber, ::Val{-2}) = inv(a^2)

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

sqrt(a::AlgebraicNumber) = ^(a, 1 // 2)
# cbrt(a::AlgebraicNumber) = ^(a, 1 // 3) # intentionally not defined - alike Complex.
isfinite(a::AlgebraicNumber) = isfinite(a.roots[a.rootid])
isreal(a::AlgebraicNumber) = isreal(approx(a))
real(a::AlgebraicNumber) = isreal(a) ? a : (a + conj(a)) / 2
imag(a::AlgebraicNumber) = isreal(a) ? zero(a) : (conj(a) - a) * AlgebraicNumber(im) / 2
abs(a::AlgebraicNumber) = !isreal(a) ? sqrt(a * conj(a)) : real(approx(a)) >= 0 ? a : -a

function *(a::T, b::T) where T<:AlgebraicNumber
    if iszero(a)
        isfinite(b) ? a : throw_D()
    elseif iszero(b)
        isfinite(a) ? b : throw_D()
    elseif !isfinite(a)
        !iszero(b) ? a : throw_D()
    elseif !isfinite(b)
        !iszero(a) ? b : throw_D()
    elseif a == b
        literal_pow(^, a, Val(2))
    else
        pab = multiply(a, b)
        AlgebraicNumber(pab, approx(a) * approx(b))
    end
end

*(a::T, aa::RingNumber) where T<:AlgebraicNumber =
    AlgebraicNumber(lincomb(minimal_polynomial(a), aa), approx(a) * fvalue(aa))
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
    elseif a == b # there should be better performance possible in this case - also check if a and b are collinear
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
    elseif iszero(aa)
        monom(T)
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
    iszero(a) && return AlgebraicNumber(Inf)
    isfinite(a) || return AlgebraicNumber(0)
    p = minimal_polynomial(a)
    q = reverse(p)
    q /= LC(q)
    AlgebraicNumber(q, inv(approx(a)))
end

# find best of irreducible factors with respect to having a root close to `a`.
function findbest(ps::AbstractVector{<:UnivariatePolynomial}, a::Number)
    rmax = -1.0
    res = []
    for pp in ps
        for p in [first(s) for s in factor(pp)]
            r = cr_roots(p)
            push!(res, (p, r))
            rmax = max(rmax, maximum(abs, r))
        end
    end
    aa = fnormed(a, rmax)

    bestd = Inf
    bestp = first(ps)
    bestr = ComplexF64[]
    for (p, r) in res
        _, b = nextroot(aa, r)
        d = abs(b - aa)
        if d < bestd
            bestd = d
            bestp = p
            bestr = r
        end
    end
    b, id = closeroot(bestp, big(fvalue(a)), bestr)
    bestp, b, bestr, id
end

fvalue(a::Number) = float(a)
fvalue(a::Ring) = value(a)

# find root of `p`, which is closest to `a`, perform root iterations for full accuracy.
function closeroot(p::UnivariatePolynomial, a::Number, r::AbstractVector{<:Number})
    p = primpart(p) # converts to ZZ[:x] - faster than QQ[:x]

    dp = derive(p)
    a = fnormed(a, maximum(abs, r))
    id, a = nextroot(a, r)
    da = p(a) / dp(a)
    epsb = abs(a) * sqrt(eps(real(typeof(a))))
    i = 100
    while true
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

function cr_roots(p::Union{<:UnivariatePolynomial,<:AbstractVector})
    A = companion(Float64, p)
    roots = LinearAlgebra.eigvals(A; permute = false, scale = false)
    map(roots) do x
        e = sqrt(eps())
        abs(real(x)) < e * abs(imag(x)) ? Complex(0, imag(x)) : x
    end
end

"""
    fnormed(a, b)

If `abs(a)`is greater than
ten times the `maximum(abs.(r))` its size is reduced to that value.
fnormed(a::Real, b::Real) = abs(a) > b ? sign(a) * b : a
"""
function fnormed(a::C, b::Real) where {T,C<:Complex{T}}
    if isfinite(a)
        abs(a) > b ? sign(a) * b : a
    else
        t = floatmax(T) / sqrt(2)
        re = clamp(real(a), -t, t)
        ig = clamp(imag(a), -t, t)
        sign(C(re, ig)) * b
    end
end
function fnormed(a::T, b::Real) where T<:Real
    abs(a) > b ? sign(a) * b : a
end

"""
    nextroot(a, r::Vector)

Find the number in `r`, which is closest to `a`.
"""
function nextroot(a::T, r::AbstractVector) where T<:Number
    _, i = findmin(r) do v
        abs(a - v)
    end
    i, Complex{float(real(T))}(r[i])
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
Base.cispi(q::Q) where Q<:QQ = _cispi(Q, fvalue(q))
function _cispi(Q::Type{<:QQ}, r::Rational{<:Integer})
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
    fs, fc = sincospi(big(fvalue(q)))
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
    fs = sinpi(big(fvalue(q))) * im
    as = AlgebraicNumber(s, fs)
    AlgebraicNumber(_squaremulim(minimal_polynomial(as)), approx(as) / im)
end
function Base.cospi(q::QQ)
    d = cispi(q)
    N = NF(d)
    a = monom(N)
    b = inv(a)
    c = (a + b) / 2
    fc = cospi(big(fvalue(q)))
    ac = AlgebraicNumber(c, fc)
    ac
end
function Base.tanpi(q::QQ)
    d = cispi(q)
    N = NF(d)
    a = monom(N)
    b = inv(a)
    c = (a - b) / (a + b)
    fc = tanpi(big(fvalue(q))) * im
    ac = AlgebraicNumber(c, fc)
    AlgebraicNumber(_squaremulim(minimal_polynomial(ac)), approx(ac) / im)
end

# only for internal usage
# assume minimal polynomial has only powers of x^2.
# simulate effect of multiplication with `im` in minimal polynomial
function _squaremulim(p::UnivariatePolynomial)
    c = copy(p)
    n = length(c.coeff)
    for k = n-2:-4:1
        c.coeff[k] = -c.coeff[k]
    end
    c
end

"""
    rationalconst(expr)

Return the value of a rational constant or a rational function of rational constants
if that can be expressed as `Rational`. Otherwise return `nothing`.
"""
rationalconst(x::Integer) = big(x)
rationalconst(x::AbstractFloat) = isinteger(x) ? Integer(x) : nothing
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
            e = rationalconst(args[3])
            isnothing(e) && return e
            en = numerator(e)
            ed = denominator(e)
            ed == 1 && return p^en
            sn = Integer(trunc(numerator(p)^(1 / ed)))
            sd = Integer(trunc(denominator(p)^(1 / ed)))
            q = sn // sd
            return q^ed == p ? q^en : nothing
        elseif fun == :inv
            p = rationalconst(args[2])
            isnothing(p) && return p
            return inv(p)
        elseif fun == :sqrt
            p = rationalconst(args[2])
            isnothing(p) && return p
            sn = isqrt(abs(numerator(p)))
            sd = isqrt(denominator(p))
            q = sn // sd
            return q^2 == p ? q : nothing
        elseif fun == :cbrt
            p = rationalconst(args[2])
            isnothing(p) && return p
            sn = Integer(trunc(cbrt(numerator(p))))
            sd = Integer(trunc(cbrt(denominator(p))))
            q = sn // sd
            return q^3 == p ? q : nothing
        end
        if fun ∉ (:(+), :(-), :(*), :(//))
            return nothing
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

const ALLOWED_SYMBOLS = (:im, :φ)

isalgebraic(::AlgebraicNumber) = true
isalgebraic(::Union{Rational,Integer}) = true
isalgebraic(x::AbstractFloat) = isinteger(x)
isalgebraic(s::Symbol) = s ∈ ALLOWED_SYMBOLS
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
        elseif fun ∉ (:(+), :(-), :(*), :(//), :inv, :sqrtx, :cbrt)
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

replacesqrt!(s::Symbol) = s === :sqrt ? :sqrtx : s
replacesqrt!(a::Any) = a
function replacesqrt!(expr::Expr)
    if expr.head == :call
        args = expr.args
        for i in axes(args, 1)
            args[i] = replacesqrt!(args[i])
        end
    end
    expr
end

sqrtx(x::Number) = sqrt(complex(x))

function AlgebraicNumber(expr::Expr, pre::Union{Nothing,Number} = nothing)
    replacesqrt!(expr)
    approx = pre === nothing ? eval(expr) : float(pre)
    A = AlgebraicNumber(to_algebraic_or_rational(expr))
    r = A.roots
    p = A.minpol
    a, id = closeroot(p, big(fvalue(approx)), r)
    AlgebraicNumber(p, r, id, a, NOCHECK)
end

function to_algebraic_or_rational(expr::Expr)
    x = rationalconst(expr)
    !isnothing(x) && return x
    isalgebraic(expr) || throw(ArgumentError("expression is not an algebraic number"))
    head = expr.head
    if head == :call
        args = expr.args
        fun = args[1]
        if fun == :(^)
            a = to_algebraic_or_rational(args[2])
            q = rationalconst(args[3])
            denominator(q) != 1 && (a = AlgebraicNumber(a))
            return a^q
        elseif fun ∈ (:(+), :(-), :(*), :(//), :(/), :inv, :sqrtx, :cbrt)
            n = length(args)
            eargs = Vector{Any}(undef, n - 1)
            for j = 2:n
                eargs[j-1] = to_algebraic_or_rational(args[j])
            end
            return evaluate(Val(fun), eargs)
        end
        throw(ArgumentError("unknown function $fun"))
    else
        throw(ArgumentError("no call, but $head"))
    end
end
to_algebraic_or_rational(a::Number) = a
function to_algebraic_or_rational(s::Symbol)
    s in ALLOWED_SYMBOLS ? AlgebraicNumber(s) : throw(ArgumentError("unexpected symbol $s"))
end

evaluate(::Val{:(+)}, args) = +(args...)
evaluate(::Val{:(-)}, args) = -(args...)
evaluate(::Val{:(*)}, args) = *(args...)
evaluate(::Val{:(/)}, args) = /(args...)
evaluate(::Val{:(//)}, args) = /(args...)
evaluate(::Val{:(inv)}, args) = inv(args...)
evaluate(::Val{:(sqrtx)}, args) = sqrt(AlgebraicNumber(args[1]))
evaluate(::Val{:(cbrt)}, args) = AlgebraicNumber(args[1])^(1 // 3)

"""
    com2(p, q)

calculates `mod(q^i, p)` for i = 0:n and stores coeffs in n*n matrix M and vector V.
The solution of the linear sytem of equations delivers the coefficients of
the field polynomial of `q(a)` when p is the minimal polynomial of `a`.

Is an alternative to `det(x - companion(p, q))` which is faster sometimes.
"""
function com2(p::UnivariatePolynomial{T}, q) where T
    n = deg(p)
    S = typeof(fvalue(p[0]))
    M = zeros(S, n, n)
    s = q^0
    for i = 0:n-1
        k = deg(s)
        for k = 0:k
            M[k+1, i+1] = s[k]
        end
        s = mod(s * q, p)
    end
    V = zeros(S, n)
    k = deg(s)
    for k = 0:k
        V[k+1] = s[k]
    end
    M, V
end

"""
    evaluate2(q::UnivariatePolynomial, a::AlgebraicNumber)

Evaluates polynomial `q` for an algebraic number `a` using algorithm `com2`.
"""
function evaluate2(q::P, a::AlgebraicNumber) where P<:UnivariatePolynomial
    p = minimal_polynomial(a)
    M, V = com2(p, q)
    m = -P(M \ V) + monom(P, deg(a))
    AlgebraicNumber(m, q(approx(a)))
end

field_matrix(a::AlgebraicNumber) = companion(minimal_polynomial(a))
norm(a::AlgebraicNumber) = minimal_polynomial(a)[0] * (-1)^deg(a)
tr(a::AlgebraicNumber) = -minimal_polynomial(a)[deg(a)-1]
discriminant(a::AlgebraicNumber) = discriminant(minimal_polynomial(a))

"""
    Map a vector of indices, all ranging from 0:bounds[i]-1, to a linear index
    based at 0
"""
function lindex(v::Vector{Int}, b::NTuple{N,<:Integer}) where N
    n = length(v)
    n <= N || throw(ArgumentError("index vector too long"))
    li = v[n]
    for i = n-1:-1:1
        li = li * b[i] + v[i]
    end
    li
end
"""
    Map a linear index to a vector of indices.
"""
function mindex(li::Integer, b::NTuple{N,<:Integer}) where N
    v = Vector{Int}(undef, N)
    for i = 1:N
        li, v[i] = fldmod(li, b[i])
    end
    v
end

# generate a Matrix, which represents the A.N. with the canonical base.
function matrixtower(A::AbstractVector{B}) where B<:AlgebraicNumber
    n = length(A) - 1
    if !isone(A[end])
        A ./= A[end]
    end
    bounds = tuple(deg.(A)...)
    N = prod(bounds)
    M = zeros(basetype(B), N * n, N * n)
    for k = 0:n-1
        buildtower!(M, k, n, bounds, A)
    end
    for i = 1:N*(n-1)
        M[i+N, i] = 1
    end
    M
end

function buildtower!(
    M::AbstractMatrix,
    k::Integer,
    n::Integer,
    bounds::NTuple,
    A::AbstractVector,
)
    N = prod(bounds)
    a = minimal_polynomial(A[k+1])
    for li = 0:N-1
        di = N * k + 1
        dj = N * (n - 1) + 1
        iv = mindex(li, bounds)
        if iv[k+1] + 1 < bounds[k+1]
            iv[k+1] += 1
            lj = lindex(iv, bounds)
            iv[k+1] -= 1
            M[lj+di, li+dj] = -1
        else
            for j = 0:bounds[k+1]-1
                iv[k+1] = j
                lj = lindex(iv, bounds)
                M[lj+di, li+dj] += a[j]
            end
            iv[k+1] = bounds[k+1] - 1
        end
    end
    M
end

# constructive way of proving algebraic completeness of AlgebraicNumbers
# Attention: the degree of the minimal polynomial explodes to the
# product of the degrees of the defining A.N. and the degree of pa itself.
function AlgebraicNumber(pa::UnivariatePolynomial{<:AlgebraicNumber})
    AlgebraicNumber(pa[:])
end

import Polynomials

function AlgebraicNumber(A::AbstractVector{<:AlgebraicNumber})
    fapprox(a::AlgebraicNumber) = a.roots[a.rootid]
    rr = cr_roots(fapprox.(A))[1]
    AlgebraicNumber(characteristic_polynomial(matrixtower(A)), rr)
end
