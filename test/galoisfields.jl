module GaloisFieldsTest

using CommutativeRings
using CommutativeRings.Conway
using Test
using Random
using LinearAlgebra

import CommutativeRings: GFImpl, log_zech, logmonom
const Polynomial = CommutativeRings.Polynomial

rng = MersenneTwister(1)
randmatrix(p::Integer, n::Integer) = rand(rng, 0:p-1, n, n)

@testset "Galois Fields Implementation" begin

    @test GFImpl(7, mod=nothing) <: ZZmod{7}
    @test GFImpl(7, mod=:conway) <: Quotient{<:UnivariatePolynomial{<:ZZmod{7}}}
    @test GFImpl(3) == GFImpl(3, 1)
    @test GFImpl(5, 3) <: Quotient{<:UnivariatePolynomial{<:ZZmod{5}}}

    G7 = GFImpl(7)
    @test G7(3)^2 == G7(2)

    G53 = GFImpl(5, 3)
    @test isone(inv(G53([1, 0, 1])) * G53([1, 0, 1]))

    x = monom(basetype(G53), 1)
    ma53(p, n, k) = Matrix{G53}(randmatrix(p, n) .* x^k)
    A = ma53(4, 3, 0) + ma53(4, 3, 1) + ma53(4, 3, 2)
    @test inv(A) * A == I

    G = GFImpl(5, 3)([1, 2, 3])
    v = varname(modulus(G))
    @test v in (:α, :β, :γ)
    @test sprint(show, G) == "3°*$v^2 + 2°*$v + 1° mod($v^3 + 3°*$v + 3°)"
end

@testset "Galois Fields" begin
    @test_throws ArgumentError GF(1)
    @test_throws ArgumentError GF(12)
    @test GF(32) == GF(2, 5)
    @test GF(625) == GF(5, 4)
end

@testset "Galois Fields $p^$r (max=$m, mod=$mod)" for (p, r) in ((2, 8), (7, 2)),
    m in (2^20, 20),
    mod in (nothing, :conway)

    @test GF(p) == GF(p, 1; maxord = m)
    @test GF(p, r; maxord = m, mod = mod) <: GaloisField
    G = GF(p, r; maxord = m, mod = mod)
    @test Quotient(G) <: Quotient{<:UnivariatePolynomial{<:ZZmod{p}}}
    Q = Quotient(G)
    P = Polynomial(G)
    @test Q == basetype(G)
    @test P / modulus(G) == Q
    @test modulus(G) == modulus(Q)
    @test order(G) == order(Q) == p^r
    @test characteristic(G) == characteristic(Q) == p
    @test dimension(G) == dimension(Q) == r
    @test deg(modulus(G)) == r

    @test G[p^r-1] isa G
    @test G[0:p^r-1] isa Vector{G}

    g1, g2 = rand(rng, G, 2)
    while iszero(g1 * g2)
        g1, g2 = rand(rng, G, 2)
    end
    @test convert(G, convert(Q, g1)) == g1
    q1, q2 = Quotient.((g1, g2))
    @test G(q1) == g1
    @test G[1] == Q(1)
    @test G[p] != G(p)
    @test q1 == Q(g1)
    @test g1 == G(q1)
    @test g1 == q1

    @test g1 * g2 == q1 * q2
    @test g1^17 == q1^17
    @test g1^-17 == q1^-17
    @test g1 + g2 == q1 + q2
    @test g1 - g2 == q1 - q2
    @test -g1 == -q1
    @test inv(g1) == inv(q1)

    @test iszero(G[0])
    @test isone(G[1])
    @test isunit(G[2])
    @test zero(G) == 0
    @test one(G) == 1
    @test G[10] / G[10] == 1
    @test one(G) * g1 == g1
    @test zero(G) * g1 == 0
    @test g1 * 1 == g1
    @test 1 * g2 == g2
    @test 2g1 == g1 + g1
    @test g2^2 == g2 * g2
    @test g1 + g1 == 2g1
    @test g1 + (-g2) == g1 - g2
    @test g1 * inv(g2) == g1 / g2
    @test (g1 - g1) - g2 == -g2
    @test_throws ArgumentError inv(G(0))
    a = 10
    @test G(0)^10 == 0
    @test G(0)^0 == 1
    @test G(0)^a == 0
    @test G(0)^(a - a) == 1
    @test_throws ArgumentError G(0)^-2

    @test sprint(show, g1) !== nothing
    @test sprint(show, q1) !== nothing
    @test endswith(sprint(show, generator(G)), r"{(0:)*1:0%[1-9]}")

    @test G(one(ZZ / p)) == one(G)
    @test length(modulus(G).(collect(G))) == length(G)

    @test value(g1) == value(q1)

    @test num_irreducibles(Polynomial(G), dimension(G)) < order(G)
    @test GF(p, r; nr = 1) !== nothing
    @test_throws ArgumentError GF(p, r, mod=nothing, nr = 10000000)

    @test log(G(0)) == -1
    @test log(one(G)) == 0
    @test log(generator(G)) == 1
    @test log(generator(G)^20) == 20
    @test det(normalmatrix(Q)) != 0

    g = generator(G)
    k = 2
    @test g^log_zech(k, G) == g^k + 1

    @test logmonom(G) == characteristic(G)

    v = ones(Int, r)
    @test Polynomial(G(v)).coeff == v
    @test monom(G) == G([0, 1])

    @test_throws ArgumentError inv(G(0))
end

@testset "Galois Field Implementation - Homomorphisms" begin

    Z1 = GFImpl(5, 2)
    Z2 = GFImpl(5, 6)
    z1 = Z1(monom(basetype(Z1)))
    iso = homomorphism(Z1, Z2)
    z2 = iso(z1)
    @test z1 != z2
    @test iso(z1) == z2
    @test z1 + 1 == z1 + Z1(1)
    @test iso(Z1(0)) == Z2(0)
    @test iso(Z1(1)) == Z2(1)
    @test iso(z1^17 + 2z1^12 + 1) == z2^17 + 2z2^12 + 1
end

@testset "normalbase" begin
    Z = ZZ / 7
    P = Z[:α]
    x = monom(P)
    Q = P / ((x + 1) * (x + 2))
    @test_throws ArgumentError CommutativeRings.normalbase(Q)
    q = irreducible(P, 6)
    Q = P / q
    @test CommutativeRings.normalbase(Q) == x^5 + x^4 + x^3 + x^2 + x + 1
end

@testset "Galois Field - Homomorphisms" begin

    Z1 = GF(5, 2)
    Z2 = GF(5, 6)
    z1 = generator(Z1)
    iso = homomorphism(Z1, Z2)
    z2 = iso(z1)
    @test z1 != z2
    @test iso(z1) == z2
    @test z1 + 1 == z1 + Z1(1)
    @test iso(Z1(0)) == Z2(0)
    @test iso(Z1(1)) == Z2(1)
    @test iso(z1^17 + 2z1^12 + 1) == z2^17 + 2z2^12 + 1

    @test modulus(Z1) == modulus(Quotient(Z1))
    @test !issimpler(z2, z2)

    x = monom(Z1[:x])
    y = monom(Z2[:x])
    p = x^2 + z1 * x
    q = y^2 + z2 * y
    @test iso(p) == q

    G = GF(47)
    h = homomorphism(x -> G(x), Int, G)
    @test h(18) == G(18)
end

@testset "Galois field - irreducibles GF{$q,$r} ^ $s" for (q, r, s) in
                                                          ((2, 3, 3), (3, 2, 3))
    G = GF(q, r)
    irr = irreducibles(G[:x], s)
    @test length(collect(irr)) == necklace(order(G), s)
    @test necklace(order(G), s) == num_irreducibles(G, s)
end

@testset "Galois field - user modulus" begin
    P = ZZ{Int}[:x]
    x = monom(P)
    p = x^3 + x + 1
    @test GF(5; mod = p) <: GaloisField
    GF125 = GF(5; mod = p)
    gen = generator(GF125)
    @test order(gen) == order(GF125) - 1
    @test monom(Quotient(GF125)) + 4 == Quotient(gen)
    @test monom(Quotient(GF125)) == Quotient(GF125[characteristic(GF125)])
    @test_throws ArgumentError GF(11, mod = p) # p not irreducible in ZZ/11
end

@testset "isprimitive $G" for G in (GF(31), GF(2^3), GF(3^4))
    gG = (x for x in G)
    ord = order(G) - 1
    @test isprimitive.(gG) == (order.(gG) .== ord)
    @test isfield(G)
end

@testset "allzeros" begin
    Z = ZZ / 7
    P = Z[:x]
    p = irreducible(P, 5)
    G = GF(7, 5)
    fa = findall(iszero, p.(collect(G)))
    vx = ofindex(first(fa) - 1, G)
    @test G[first(fa)-1] == vx
    @test sort(collect(allzeros(p, vx))) == ofindex.(fa .- 1, Ref(G))
end

@testset "Conway" begin
    @test GF(67, 18; mod = :conway)(ones(Int, 18)) isa GaloisField
    @test GF(109987, 2; mod = :conway) <: GaloisField

    @test ismissing(conway(17, 32))
    poly = conway(17, 30)
    @test Conway.has_conway_property(poly)

    @test length(Conway.conway_multi(5, 3)) == 10
    @test Conway.conway_multi(3, 6; nr = 1)[1] == conway(3, 6)

    c = Conway.conway_multi(19, 4; nr = 2)
    @test is_conway(GF(19, mod=c[1])) == true
    @test is_conway(GF(19, mod=c[2])) == false
    @test is_conway(GF(19, 4, mod=nothing)) == false
end

@testset "sqrt" begin
    G = GF(2, 5)
    cG = collect(G)
    @test sqrt(G[0]) == 0
    @test sqrt(G[1]) == 1
    @test all(sqrt.(cG) .^ 2 .== cG)

    G = GF(3, 5)
    cG = collect(G)
    @test_throws DomainError sqrt(G[14])
    @test sqrt(G[13]^2) == G[13]
    @test sqrt(G[14]^2) == -G[14]
    @test all((sqrt.(cG .^ 2) .== cG) .| (sqrt.(cG .^ 2) .== .-cG))
end

end #module
