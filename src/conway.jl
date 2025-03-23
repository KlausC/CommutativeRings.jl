module Conway

export conway, is_conway, quasi_conway

using Primes
using ..CommutativeRings
using CommutativeRings: intpower, _isprimitive, coeffs

const CONWAY_POLYNOMIALS = Dict{Tuple{Int,Int},Any}()

function store_conway!(row::Vector)
    p, n, c = row
    key = (p, n)
    @assert c[n+1] == 1
    c = c[1:n]
    ix = findlast(!iszero, c)
    if ix !== nothing && ix > 0
        resize!(c, ix)
    end
    d = CONWAY_POLYNOMIALS
    d[key] = c
end

function store_conway!(poly::P) where P<:UnivariatePolynomial{<:ZZmod}
    c = value.(coeffs(poly))
    p = characteristic(P)
    map!(x -> x >= 0 ? x : p + x, c, c)
    n = deg(poly)
    store_conway!([p, n, c])
end

"""
    conway(p, n)

Return the conway-polynomial of degree `n` over `ZZ/p`, as far as available.

For `n in (1,2)` the polynomials are calculated and memoized in the data cache.
"""
function conway(p::Integer, n::Integer, X::Symbol = :x)
    isprime(p) || throw(ArgumentError("p is not prime ($p)"))
    n > 0 || throw(ArgumentError("n is not positive ($n)"))

    c = get(CONWAY_POLYNOMIALS, (p, n), missing)
    if ismissing(c) && n <= 2
        poly = quasi_conway(p, n, X)
        store_conway!(poly)
        return poly
    end
    ismissing(c) && return c
    B = (ZZ/p)[X]
    B(c) + monom(B, n)
end

"""
    is_conway(::Type{GaloisField})

Return true, iff the modulus of the field is the standard conway polynomial.
"""
function is_conway(::Type{G}) where {G<:Union{GaloisField,Quotient{<:UnivariatePolynomial}}}
    p = modulus(G)
    p == conway(characteristic(G), dimension(G), varname(p))
end
is_conway(a::Type{Union{}}) = merror(is_conway, (a,))

"""
    quasi_conway(p, m, X::Symbol, nr::Integer=1, factors=nothing)

Return the first irreducible polynomial over `ZZ/p` of degree `m`.

The polynomials are scanned in the canonical order for Conway polynomials.

Variable symbol is `X`. If given, `factors` must be the prime factorization of `m`.
If `nr > 0` is given, the `nr+1`^st of found polynomials is returned.
"""
function quasi_conway(p::Integer, m::Integer, X::Symbol = :x; nr = 0, factors = nothing)
    Z = ZZ / p
    P = Z[X]
    fact = factors === nothing ? factor(intpower(p, m) - 1) : factors
    mm = prod(fact)
    x = monom(P)
    g = generator(Z)
    s = (-1)^(m - 1)
    nx = max(nr, 0)
    # find the next irreducible, for which x is primitive (drop first nr-1)
    for poly in Monic(P, m - 1)
        gen = (poly(-x) * x - g) * s # observation for all calculated Conway polynomials
        if isirreducible(gen) && _isprimitive((x, gen), mm, fact)
            nx == 0 && return gen
            nx -= 1
        end
    end
    text = "no irreducible polynomial of degree $m found with generator '$X' (nr = $nr)"
    throw(ArgumentError(text))
end

"""
    conway_multi(p, m, X=:x; nr=10^5)

Return a list of conway polynomials for `GF(p^m)`, length clipped to `nr.
"""
function conway_multi(p::Integer, m::Integer, X::Symbol = :x; nr = 10^5, factors = nothing)
    Z = ZZ / p
    P = Z[X]
    fact = factors === nothing ? factor(intpower(p, m) - 1) : factors
    mm = prod(fact)
    x = monom(P)
    g = generator(Z)
    s = (-1)^(m - 1)
    nx = max(nr, 0)
    res = []
    # find the next irreducible, for which x is primitive (drop first nr-1)
    for poly in Monic(P, m - 1)
        gen = (poly(-x) * x - g) * s # assuming gen[0] == g * (-1)^m
        if has_conway_property2(gen, fact) && has_conway_property3(gen)
            push!(res, gen)
            nx <= 1 && break
            nx -= 1
        end
    end
    res
end

function has_conway_property(p::Polynomial)
    has_conway_property1(p) && has_conway_property2(p) && has_conway_property3(p)
end

"""
    has_conway_property1(poly)

Check if `poly` is monomial.
"""
function has_conway_property1(poly::T) where {P,S<:ZZmod{P},T<:UnivariatePolynomial{S}}
    ismonic(poly)
end

"""
    has_conway_property2(poly)

Check if an irreducible polynomial `poly` over `ZZ/p` of degree `n` has property 2 (is primitive).

That means that the standard generator `x` in the quotient ring (field) `(ZZ/p) / poly`
is also generator in the multiplicative group of the ring.

If `m` is the order of this group (`p^n - 1` if a field), it sufficient to check, if
`x ^ (m / s)` != 1 for all prime factors of `m`. (`y ^ m == 1` for all `y != 0`)

The function returns `missing` if `p^n - 1` has no known prime factors.
"""
function has_conway_property2(
    poly::T,
    factors = nothing,
) where {P,S<:ZZmod{P},T<:UnivariatePolynomial{S}}
    p = P
    m = deg(poly)
    fact = factors === nothing ? Primes.factor(intpower(p, m) - 1) : factors
    mm = prod(fact)
    isirreducible(poly) || return false
    x = monom(T)
    _isprimitive((x, poly), mm, fact)
end

"""
    has_conway_property3(poly::(ZZ/p)[:x]})

Check if a polynomial `poly` over `ZZ/p` of degree `n` has property 3.

That means, for all divisors `1 <= m < n` we have
`conway(p, m)(x^w) == 0 mod poly` with `w = (p^n - 1) / (p^m - 1)`.

The definition is recursive and requires the knowledge of Conway polynomials of lesser degree.

If such polynomials are unknown, `missing` is returned.
"""
function has_conway_property3(poly::T) where {P,S<:ZZmod{P},T<:UnivariatePolynomial{S}}
    n = deg(poly)
    p = P
    Q = T / poly
    for m in factors(n)
        if m < n
            nm = n ÷ m
            q = big(p)^m
            # w = (p^n - 1) / (p^m - 1); Z = x^w mod poly
            X = monom(Q)
            Y = X^q
            Z = X * Y
            for i = 2:nm-1
                Y = Y^q
                Z *= Y
            end
            w = (q^nm - 1) ÷ (q - 1)
            @assert X^w == Z
            c = conway(p, m)
            ismissing(c) && return missing
            !iszero(c(Z)) && return false
        end
    end
    return true
end

function readparse(fn::AbstractString, action::Function)
    open(fn, "r") do io
        readparse(io, action)
    end
end
function readparse(io::IO, action::Function)
    while !eof(io)
        line = readline(io)
        if line[1] == '[' && line[end] == ','
            row = eval(Meta.parse(line[1:end-1]))
            action(row)
        end
    end
end

function __init__()
    # file imported from
    # `https://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/CPimport.txt.gz`
    # at 2023-11-11
    if ccall(:jl_generating_output, Cint, ()) == 0   # if we're not precompiling...
        file = joinpath(@__DIR__, "..", "data", "CPimport.txt")
        empty!(CONWAY_POLYNOMIALS)
        readparse(file, r -> store_conway!(r))
    end
end

end # module
