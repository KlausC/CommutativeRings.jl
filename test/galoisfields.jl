
using Random
using LinearAlgebra

import CommutativeRings: GFImpl

let rng = MersenneTwister(1), x
mat(p::Integer, n::Integer) = rand(rng, 0:p-1, n, n)

@testset "Galois Fields Implementation" begin
    
    @test GFImpl(7) <: ZZmod{7}
    @test GFImpl(3) == GFImpl(3,1)
    @test GFImpl(5,3) <: Quotient{X,<:UnivariatePolynomial{:γ,<:ZZmod{5}}} where X
    
    G7 = GFImpl(7)
    @test G7(3)^2 == G7(2)

    G53 = GFImpl(5,3)
    @test inv(G53([1,0,1])) * G53([1,0,1]) == 1
   
    x = monom(basetype(G53), 1)
    ma53(p, n, k) = Matrix{G53}(mat(p, n) .* x^k)
    A = ma53(4, 3, 0) + ma53(4, 3, 1) + ma53(4, 3, 2)
    @test inv(A) * A == I

    io = IOBuffer()
    show(io, GFImpl(5,3)([1,2,3]))
    s = String(take!(io))
    @test s == "{3:2:1%5}"
end

@testset "Galois Fields $p^$r" for (p, r) in ((2,10), (7,2))
    
    @test GF(p) == GF(p,1)
    @test GF(p, r) <: GaloisField{p^r}
    G = GF(p, r)
    @test basetype(G) <: Quotient{X,<:UnivariatePolynomial{:γ,<:ZZmod{p}}} where X
    Q = basetype(G)
    @test modulus(G) == modulus(Q)
    @test order(G) == order(Q)
    @test characteristic(G) == characteristic(Q)
    @test dimension(G) == r

    g1, g2 = rand(rng, G, 2)
    @test convert(G, convert(Q, g1)) == g1
    q1, q2 = convert.(Q, (g1, g2))
    @test G(1) == Q(1)
    @test G(p) != Q(p)
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

    @test iszero(G(0))
    @test isone(G(1))
    @test isunit(G(2))
    @test zero(G) == 0
    @test one(G) == 1
    @test G(10) / G(10) == 1
    @test one(G) * g1 == g1
    @test zero(G) * g1 == 0
    @test g1 * 1 == g1
    @test 1 * g2 == g2
    @test 2g1 == g1 + g1
    @test g2 ^ 2 == g2 * g2
    @test_throws ArgumentError inv(G(0))
    @test_throws ArgumentError G(0) ^ -2

    @test sprint(show, g1) == sprint(show, q1)

end

@testset "Galois Field Implementation - Homomorphisms" begin

    Z1 = GFImpl(3, 2)
    Z2 = GFImpl(3, 6)
    z1 = Z1([0, 1])
    iso = isomorphism(Z1, Z2)
    z2 = iso(z1)
    @test iso(Z1(0)) == Z2(0)
    @test iso(Z1(1)) == Z2(1)
    @test iso(z1^17 + 2z1^12 + 1) == z2^17 + 2z2^12 + 1

end

end
