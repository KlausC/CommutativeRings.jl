module FactorizationTest

using Test
using CommutativeRings

@testset "irreducibles $p" for p in (2, 3)
    Z = ZZ / p
    n = 5
    irrn = collect(irreducibles(Z[:x], n))
    @test irreducible(Z[:x], n) == irrn[1]
    @test irreducible(Z[:x], n, 4) == irrn[5]
    @test length(irrn) == necklace(p, n)
    m = 7
    irrm = collect(irreducibles(Z[:x], m))
    f = prod(irrn[2:4]) * prod(irrm[3:4]) * irrn[2]
    @test isreducible(f)
    ff = factor(f)
    @test length(ff) == 5
    @test prod(ff) == f

    @test length(irrn) == num_irreducibles(Z[:x], n)
    @test length(irrn) == necklace(p, n)
    @test length(irrm) == necklace(p, m)

    redn = collect(reducibles(Z[:x], n))
    @test reducible(Z[:x], n) == redn[1]
    @test reducible(Z[:x], n, 4) == redn[5]
    @test length(redn) + length(irrn) == p^n
end

@testset "factor non-monic" begin
    Z = ZZ / 3
    x = monom(Z[:x])
    p = x^0*2
    @test CommutativeRings.ddf(p) == [(ZZ/3)(2) => 1]
    p = (-x + 1)^9
    @test prod(factor(p)) == p
    p = zero(p)
    @test factor(p) == [p => 1]
    p = one(p)
    @test factor(p) == [p => 1]
    p = x + 1
    @test factor(p) == [p => 1]
    p = -x + 1
    @test factor(p) == [-one(x) => 1, x - 1 => 1]
    p = -(x + 1)^3
    @test factor(p) == [-one(x) => 1, x + 1 => 3]
end

@testset "random polynomials" begin
    P = (ZZ/31)[:x]
    x = monom(P)
    p = x^5 + 1
    Q = P / p
    @test rand(Q) isa Q
    @test deg(value(rand(Q))) == deg(p) - 1
end

end # module
