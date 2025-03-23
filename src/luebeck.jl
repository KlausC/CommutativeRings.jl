"""
    StandardGenerators

Implementation of the algorithms by Frank Lübeck:

Standard Generators of Finite Fields and their
Cyclic Subgroups
Frank Lübeck
June 22, 2022

arXiv:2107.02257v2 [math.AC] 21 Jun 2022
https://arxiv.org/pdf/2107.02257
"""
function StandardGenerators end

"""
    standard_affine_shift(q:Integer, i::Integer)

Return `mod(m * i + a, q)` where the greatest integer `m <= 4q/5` with `gcd(m, q) == 1`
and the greatest integer `a <= 2q/3`.

For each `q > 1` the map `i -> standard_affine_shift(q, i)` is a bijection of `0:q-1`.
The function serves as a standardized quasi random generator to traverse this range.

Definition 2.7
"""
function standard_affine_shift(q::Integer, i::Integer)
    a = q - 1 - div(q - 1, 3)
    m = q - 1 - div(q - 1, 5)
    while gcd(m, q) != 1
        m -= 1
    end
    add_ZZmod(mult_ZZmod(m, i, q), a, q - a)
end

"""
    steinitz_number(x::Q) where Q<:Union{ZZmod,Quotient,GaloisField}

Return a unique number for `x` in the range `0:order(Q)-1`.

The quotient must represent a finite field
(residual class of UnivariatePolynomial{F} where F represents a finite field).

Definition 3.4
"""
function steinitz_number(x::Q) where {P,Q<:Quotient{<:UnivariatePolynomial{P}}}
    cc = coeffs(value(x))
    evalpoly(order(P), steinitz_number.(cc))
end
function steinitz_number(x::G) where G<:Union{GaloisField,ZZmod}
    tonumber(x)
end

"""
    steinitz_element(::Type{Q}, r::Integer) where Q<:Union{ZZmod,GaloisField,Quotient}

Return the element of `x` of type `Q` with `steinitz_number(x) == r`.
"""
function steinitz_element(
    ::Type{Q},
    r::Integer,
) where Q<:Union{ZZmod,GaloisField,Quotient,UnivariatePolynomial}
    # order(Q) > 0 || throw(ArgumentError("Only for finite fields"))
    # 0 <= r < order(Q) || throw(ArgumentError("element number must be in range"))
    _steinitz_element(Q, r)
end

function _steinitz_element(::Type{Q}, r::Integer) where Q<:Union{ZZmod,GaloisField}
    ofindex(r, Q)
end

function _steinitz_element(::Type{Q}, r) where {P,U<:UnivariatePolynomial{P},Q<:Quotient{U}}
    Q(_steinitz_element(U, r))
end

function _steinitz_element(::Type{U}, r::Integer) where {P,U<:UnivariatePolynomial{P}}
    p = order(P)
    res = zero(U)
    i = 0
    while !iszero(r)
        r, s = fldmod(r, p)
        res += monom(U, i) * _steinitz_element(P, s)
        i += 1
    end
    res
end

"""
    find_non_rth_power(::F, r)

Return an element of `F` which is not `x^r` for any `x ∈ F`.

`r` must divide `order(F)-1`.

Algorithm 5.2
"""
function find_non_rth_power(::Type{F}, r::Integer) where F
    find_non_rth_power(F, r, category_trait(F))
end
function find_non_rth_power(::Type{F}, r::Integer, ::Type{<:FieldTrait}) where F
    p = order(F)
    isprime(r) || throw(ArgumentError(lazy"r must be prime but is $r"))
    mod(p - 1, r) == 0 || throw(ArgumentError(lazy"r must divide $(p-1) but is $r"))
    q = (p - 1) ÷ r
    i = 0
    while true
        i += 1
        a = steinitz_element(F, i)
        isone(a^q) || return a
    end
end

"""
    find_irreducible_polynomial(P::Type{<:UnivariatePolynomial{K}}, r:Int, a::Any)

Find irreducible polynomial of degree `r` in `P`,
using hint `a`, which can be converted to `K` (`x^r + x + K(a)` is tried first).

Algorithm 5.5
"""
function find_irreducible_polynomial(
    ::Type{P},
    r::Integer,
    a::RingInt,
) where {K,P<:UnivariatePolynomial{K}}
    q = order(K)
    inc = ilog(q, 2r - 1) + 1 # minimal integer with q^inc ≥ 2r
    d = 0   # (random coeffs up to X^d)
    x = monom(P)
    f = x^r + x + K(a)   # (first polynomial to try)
    count = 0
    while isreducible(f) # && ismonomprimitive(f)
        if mod(count, r) == 0
            # (after any r trials we allow inc more non-zero coefficients)
            d = min(d + inc, r - 1)
        end
        s = standard_affine_shift(intpower(q, d), count)
        g = steinitz_element(P, s)
        f = x^r + g * x + a
        count += 1
    end
    return f
end

function next_irreducible(::Type{P}, r::Integer) where P<:UnivariatePolynomial
    p = characteristic(P)
    isprime(r) || throw(ArgumentError(lazy"r ($r) is not prime"))
    if r == p
        next_irreducible(P, r, Val(1))
    elseif r != 2 && mod(p - 1, r) == 0 || r == 2 && mod(p - 1, 4) == 0
        next_irreducible(P, r, Val(2))
    elseif r == 2 && mod(p + 1, 4) == 0
        next_irreducible(P, r, Val(3))
    else # r != p && r != 2 && mod(p-1, r) != 0
        next_irreducible(P, r, Val(4))
    end
end
"""

Chapter 5.1 case r = p
"""
function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{1},
) where {K<:Union{ZZmod,GaloisField},P<:UnivariatePolynomial{K}}

    p = characteristic(K)
    r == p || throw(ArgumentError(lazy"r == p case, but $r != $p"))
    x = monom(P)
    ord = order(K)
    i = p
    s = K(1)
    while i < ord
        s *= steinitz_element(K, i)
        i *= p
    end
    x^r - x - s^(p - 1)
end

function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{1},
) where {K<:Quotient,P<:UnivariatePolynomial{K}}

    p = characteristic(K)
    r == p || throw(ArgumentError(lazy"r == p case, but $r != $p"))
    s = monom(K)
    k = K
    while true
        k = eltype(k)
        if k <: Quotient
            s *= monom(k)
        else
            break
        end
    end
    x = monom(P)
    x^r - x - s^(p - 1)
end

"""

Chapter 5.2 case r | (p-1) and 4 | (p-1) if r = 2
"""
function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{2},
) where {K<:ZZmod,P<:UnivariatePolynomial{K}}

    p = characteristic(K)
    mod(p - 1, r) == 0 ||
        (r == 2 && mod(p - 1, 4) == 0) ||
        throw(ArgumentError(lazy"r | p-1 case, but r = $r  p = $p"))

    x = monom(P)
    a = find_non_rth_power(K, r)
    x^r - a
end

function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{2},
) where {K<:QuotientRing,P<:UnivariatePolynomial{K}}

    p = characteristic(K)
    mod(p - 1, r) == 0 ||
        (r == 2 && mod(p - 1, 4) == 0) ||
        throw(ArgumentError(lazy"r | p-1 case, but r = $r  p = $p"))

    monom(P, r) - P(monom(K))
end

"""

Chapter 5.3 case r = 2 and 4 | (p+1)
"""
function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{3},
) where {K<:ZZmod,P<:UnivariatePolynomial{K}}

    p = characteristic(K)
    (r == 2 && mod(p + 1, 4) == 0) || throw(ArgumentError(lazy"4 | p-1 case, but p = $p"))

    monom(P, r) + 1
end

function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{3},
) where {K<:QuotientRing,P<:UnivariatePolynomial{K}}

    p = characteristic(K)
    (r == 2 && mod(p + 1, 4) == 0) || throw(ArgumentError(lazy"4 | p-1 case, but p = $p"))
    KK = subfield(K)
    if dimension(KK) == 1
        a = find_non_rth_power(K, r)
        monom(P, r) - P(a)
    else
        monom(P, r) - P(monom(K))
    end
end

"""

Chapter 5.4 case r != p and not r | (p-1)
"""
function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{4},
) where {K<:ZZmod,P<:UnivariatePolynomial{K}}

    find_irreducible_polynomial(P, r, -1)
end
function next_irreducible(
    ::Type{P},
    r::Integer,
    ::Val{4},
) where {K<:QuotientRing,P<:UnivariatePolynomial{K}}

    find_irreducible_polynomial(P, r, -monom(K))
end

function tower(B::Type{<:QuotientRing}, r::Integer, t::Integer, G::Type{<:QuotientRing})
    G = NType(G)
    dimension(B) == 1 || throw(ArgumentError("dimension of base type must be 1"))
    p = characteristic(B)
    Gi = B
    F = Vector{Any}(undef, t)
    for i = 1:t
        Pi = Gi[Symbol("X", tosub(r), Char(0x0327), tosub(i))] # REPL: \c
        fi = next_irreducible(Pi, r)
        Gi = tower_builder(G, p, fi)
        F[i] = (Gi, fi)
    end
    F
end

tower_builder(::NType{<:GaloisField}, p, fi) = GF(p; mod=fi)
tower_builder(::NType{<:Quotient}, p, fi) = typeof(fi) / fi

function matrix(g::G) where G<:GaloisField
    n = dimension(G)
    M = Matrix{ZZ/characteristic(G)}(undef, n, n)
    for i = 0:n-1
        flatgalois!(g^i, view(M, 1:n, i+1))
    end
    M
end

function flatgalois(g::G) where G<:GaloisField
    A = Vector{ZZ/characteristic(G)}(undef, dimension(G))
    flatgalois!(g, A)
    A
end

function flatgalois!(g::G, A::AbstractVector) where G<:QuotientRing
    n = length(A)
    if n == 1
        A[1] = g
    else
        v = coeffs(Polynomial(g))
        m = dimension(subfield(G))
        for i = 1:length(v)
            flatgalois!(v[i], view(A, (i-1) * m + 1:i*m))
        end
        for j = length(v)*m+1:n
            A[j] = 0
        end
    end
end

function flatgalois(::Type{G}) where G<:GaloisField
    p = characteristic(G)
    r = dimension(G)
    g = generator(G)
    M = matrix(g)
    f = flatgalois(g^r)
    w = M \ f
    P = (ZZ/p)[:x]
    mod = monom(P, r) - P(w)
    GF(p; mod)
end
