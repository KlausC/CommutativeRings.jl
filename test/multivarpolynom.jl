module MultivarTest

using Test
using CommutativeRings
using CommutativeRings: ord2expo, expo2ord, cbin, varnames
using CommutativeRings: generatorset, varnameset, varblocks, DeepIterPolynomial


Z = ZZ{Int}

@testset "index calculations" begin

    @test_throws ArgumentError cbin(0, 0)
    @test cbin(0, 1) == (0, 0)
    @test cbin(10, 1) == (10, 10)
    @test cbin(10, 9) == (10, 10)
    @test cbin(100, 9) == (11, 55)

    @test_throws ArgumentError ord2expo(0, 1) == [7654320]
    @test ord2expo(7654321, 1) == [7654320]
    @test expo2ord([1234]) == 1235
    @test ord2expo(1, 3) == [0, 0, 0]
    @test expo2ord([0, 0, 0, 0]) == 1
    @test ord2expo(binomial(20 + 4 - 1, 4) + 1, 4) == [0, 0, 0, 20]
    @test expo2ord([0, 0, 10]) == binomial(10 + 3 - 1, 3) + 1

    @test expo2ord.(ord2expo.(1:10000, 2)) == 1:10000
    @test expo2ord.(ord2expo.(1:10000, 5)) == 1:10000
end

@testset "constructors" begin

    @test Z[] == Vector{Z}(undef, 0)
    @test Z[:x] <: UnivariatePolynomial
    @test Z[:x, :y] <: MultivariatePolynomial
    @test Z[[:x], [:y]] <: MultivariatePolynomial
end

@testset "varnames and generators $P" for P in (Z[:x, :y, :z], Z[[:x], [:y, :z]])
    x, y, z = monom.(P, [[1, 0, 0], [0, 1, 0], [0, 0, 1]])
    @test [x, y, z] == generators(P)
    @test varnames(P) == [:x, :y, :z]
    @test varnames(P(0)) == [:x, :y, :z]

    p = 3x^3 * y + 4x^2 * y^2 + 5x * y * z^2
    @test deg(p) == 4
    @test multideg(p) == [3, 1, 0]
    @test LC(p) == 3
    @test LM(p) == x^3 * y
    @test LT(p) == 3 * x^3 * y
    @test CC(p) == 0
    @test p[2, 2, 0] == 4
    @test_throws ArgumentError p[2, 2]

    @test basetype(p) == Z
    @test copy(p) == p
    q = copy(p)
    q.coeff[1] = 100
    @test p.coeff[1] == 5
    @test q.coeff[1] == 100
end

@testset "addition" for P in (Z[:x, :y], Z[[:x], [:y]])

    @test zero(P) + one(P) == one(P)
    @test one(P) + one(P) == 2 * one(P)
    @test -one(P) + one(P) == zero(P)
    @test -one(P) == (-1) * one(P)
    @test one(P) - one(P) == zero(P)

    x, y = generators(P)
    a = 4 * x^3 + 3
    b = y + 5 * x^3
    @test 5a - 4b == -4y + 15
    @test a + b == 9 * x^3 + y + 3
    @test deg(zero(P)) == -1
    @test deg(one(P)) == 0
    @test deg(x + 1) == 1
    @test deg(x * y + 1) == 2
end

@testset "multiplication" for P in (Z[:x, :y], Z[[:x], [:y]])

    @test zero(P) * zero(P) == zero(P)
    @test zero(P) * one(P) == zero(P)
    @test one(P) * one(P) == one(P)
    x, y = generators(P)
    @test 0 * x == zero(P)
    @test x * 1 === x
    @test (x + y)^2 == x^2 + 2x * y + y^2
    @test (x + y) * (x - y) == x^2 - y^2
    xy = x * 5 + 2y^2 + x * y
    @test one(P) * xy == xy
    @test xy * zero(P) == zero(P)
    @test xy^2 == 25x^2 + x^2 * y * 10 + 20x * y^2 + x^2 * y^2 + 4x * y^3 + 4y^4
    @test xy * x == 5x^2 + 2x * y^2 + x^2 * y

    R = (ZZ/12)[:x, :y]
    xr = monom(R, [1, 0])
    @test (xr * 3) * 4 == zero(R)
end

@testset "division" begin
    P = ZZ{BigInt}[:x, :y]
    u, v = generators(P)
    f = u^2 - v
    g = u^3 - u
    G = [f, g]
    h = f * (u^2 + v^2) + g * (u + v) + 1
    a, r, d = pdivrem(h, G)
    @test d == 1
    @test sum(a .* G) + r == h

    @test 256 * a / (-8) == -32 * a

    @test rem(u + v, one(P)) == 0
    s, r = divrem(u + v, one(P))
    @test iszero(r) && s == u + v
end

@testset "Gröbner base $(varblocks(P))" for P in (Z[:x, :y], Z[[:x], [:y]])
    u, v = generators(P)
    @test groebnerbase([u, u]) == [u]
    @test hash(0 * u) == hash(0)
    @test hash(u^0) == hash(1)
    f = u^2 - v
    g = u^3 - u
    @test groebnerbase([f, g]) == [u^2 - v, u * v - u, v^2 - v]
end

@testset "blocked order" begin
    P = Z[[:t], [:x, :y]]
    t, u, v = generators(P)
    @test (t + 1)^2 == t^2 + 2 * t + 1
    @test (v + 1)^2 == v^2 + 2 * v + 1
    @test (u + t)^2 == u^2 + 2 * u * t + t^2
    @test (u + v)(1, 2, 3) == 5
    @test (t * u^2 * v^3 + 1)(1, 2, 3) == 1 * 4 * 27 + 1
end

@testset "conversions" for P in (Z[:t, :x, :y], Z[[:t], [:x, :y]])
    t, u, v = generators(P)
    @test generators(P) == [t, u, v]

    Q = Z[:x]
    xq = monom(Q)
    @test P(0 * xq) isa P
    @test P(0 * xq) == zero(P)
    @test P(5 * xq^0) == 5
    @test P(xq) == monom(P, [0, 1, 0])

    R = Z[:z]
    zr = monom(R)
    @test P(0 * zr) isa P
    @test P(0 * zr) == zero(P)
    @test P(5 * zr^0) == 5
    @test_throws ArgumentError P(zr)

    Q = Z[:y, :x]
    yq, xq = monom(Q, [1, 0]), monom(Q, [0, 1])
    @test P(0 * xq) isa P
    @test P(0 * yq) == zero(P)
    @test P(5 * xq^0) == 5
    @test P(xq) == monom(P, [0, 1, 0])
    @test P(xq + yq * xq) == u + v * u

    Q = Z[:z, :y, :x]
    zq, yq, xq = monom(Q, [1, 0, 0]), monom(Q, [0, 1, 0]), monom(Q, [0, 0, 1])
    @test P(0 * xq) isa P
    @test P(0 * yq) == zero(P)
    @test P(5 * xq^0) == 5
    @test P(xq) == monom(P, [0, 1, 0])
    @test P(xq + yq * xq) == u + v * u
    @test_throws ArgumentError P(zq + xq + yq)
end

@testset "extension and elimination" begin
    Z = ZZ / 7583
    P = Z[:x, :y]
    u, v = generators(P)
    A = [u^2 - v^2, v^3 - 2u * v - v^2 + 2u, u * v^2 - 3u * v + 2u]
    B = [u * v]
    Q = lextend(P, :t)
    ida = Ideal(A)
    idb = Ideal(B)
    t, = generators(Q)
    idcQ = Ideal([Q.(A) .* t; Q.(B) .* (1 - t)])
    idc = Ideal{P}(P.([x for x in idcQ.base if multideg(x)[1] == 0]))
    @test idc == intersect(ida, idb)
end

@testset "derivatives" begin
    P = Z[:x, :y]
    u, v = generators(P)
    @test derive(u, (1, 0)) == u^0
    @test derive(u, (0, 1)) == 0
    @test derive(u * v^10, (1, 1)) == 10 * v^9
    @test derive((u + 2v)^4, (0, 0)) == (u + 2v)^4
    @test_throws ArgumentError derive(u * v, (-1, 0))
end

@testset "subresultant" begin
    S = ZZ{BigInt}[:a, :b, :c]
    P = S[:x]
    a, b, c = generators(S)
    u = monom(P)
    p = u^4 + a * u^2 + b * u + c
    sresp, sres = signed_subresultant_polynomials(p, derive(p))
    @test LC.(sresp) == sres
    @test sresp[5] == p
    @test sresp[4] == derive(p)
    @test sresp[3] == -8 * a * u^2 - 12 * b * u - 16 * c
    @test sresp[2] == (-8 * a^3 - 36 * b^2 + 32 * a * c) * u - 4 * a^2 * b - 48 * b * c
    @test sresp[1] ==
          -4 * a^3 * b^2 + 16 * a^4 * c - 27 * b^4 + 144 * a * b^2 * c - 128 * a^2 * c^2 +
          256 * c^3
end


import CommutativeRings: splitpoly, joinpoly

@testset "split/join poly $var" for var in ([:x, :y, :z], [[:x], [:y], [:z]])
    S = ZZ{BigInt}
    P = S[var...]
    u, v, z = generators(P)
    p = u^2 + u * v + u + v + z + 1
    q = splitpoly(p, [:x, :y] => [:a, :b], [:z])
    Q = S[:z][:a, :b]
    @test typeof(q) == Q
    q = splitpoly(p, [:x, :y] => [:a, :b], [[:z]])
    Q = S[[:z]][:a, :b]
    @test typeof(q) == Q
    q = splitpoly(p, [:x] => [:a], [:y, :z])
    Q = S[:y, :z][:a]
    @test typeof(q) == Q
    q = splitpoly(p, [:x] => [:a], [:y], [:z] => [:c])
    Q = S[:c][:y][:a]
    @test typeof(q) == Q
    pp = joinpoly(q, [:a, :y])
    @test typeof(pp) == S[:c][:a, :y]
end

P = QQ{Int}[:u, :v, :w]
u, v, w = generators(P)
e(i::Integer) = elementary_symmetric(P, i)

@testset "elementary symmetric functions" begin
    @test e(-1) == 0
    @test e(0) == 1
    @test e(1) == u + v + w
    @test e(2) == u * v + u * w + v * w
    @test e(3) == u * v * w
    @test e(4) == 0
end

@testset "newton_symmetric" begin
    s = newton_symmetric(e(0))
    E1, E2, E3 = generators(typeof(s))
    E0 = oftype(E1, 1)

    @test newton_symmetric(e(0)) == E0
    @test newton_symmetric(e(1)) == E1
    @test newton_symmetric(e(2)) == E2
    @test newton_symmetric(e(3)) == E3

    p = e(0) + e(2)^3 + 2e(3)^2 - 5e(1) * e(2)
    @test newton_symmetric(p) == E0 + E2^3 + 2 * E3^2 - 5 * E1 * E2
    @test newton_symmetric(p)(e(1), e(2), e(3)) == p

    p = u^2 * v + u * v^2 + u^2 * w + u * w^2 + v^2 * w + v * w^2
    @test newton_symmetric(p) == E1 * E2 - 3 * E3
    @test newton_symmetric(p)(e(1), e(2), e(3)) == p

    p = u^3 * v + u * v^3 + u^3 * w + u * w^3 + v^3 * w + v * w^3
    @test newton_symmetric(p) == E1^2 * E2 - 2 * E2^2 - E1 * E3
    @test newton_symmetric(p)(e(1), e(2), e(3)) == p

    @test_throws ArgumentError newton_symmetric(p + u)

    p =
        u^10 * v^10 * w^10 +
        u^3 * v +
        u^3 * w +
        u^2 * v^2 +
        2 * u^2 * v * w +
        u^2 * w^2 +
        u * v^3 +
        2 * u * v^2 * w +
        2 * u * v * w^2 +
        u * w^3 +
        u +
        v^3 * w +
        v^2 * w^2 +
        v * w^3 +
        v +
        w +
        1
    @test newton_symmetric(p) == E1^2 * E2 - E1 * E3 + E1 - E2^2 + E3^10 + 1
    @test newton_symmetric(p)(e(1), e(2), e(3)) == p
end

@testset "compatibilty with univariate" begin
    Z = ZZ{Int}
    P = Z[:x]
    Q = P[:y]
    @test_throws ArgumentError P[:x]
    R = Q[:a, :b]
    a, b, y, x = generatorset(R)
    p = x^2 + 3
    r = a * b^2 * y * p + (p - 2)^2
    @test r isa R
    @test varnameset(R) == [:a, :b, :y, :x]
    c = collect(DeepIterPolynomial(r))
    @test c[1] == (1, [0, 0, 0, 0])
    @test c[2] == (2, [0, 0, 0, 2])
    @test c[3] == (1, [0, 0, 0, 4])
    @test c[4] == (3, [1, 2, 1, 0])
    @test c[5] == (1, [1, 2, 1, 2])
end

end # module
