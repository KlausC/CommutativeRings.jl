

@testset "irreducibles $p" for p = (2, 3)
    Z = ZZ/p
    n = 5
    irrn = collect(irreducibles(Z[:x], n))
    @test irreducible(Z[:x], n) == irrn[1]
    @test length(irrn) == necklace(p, n)
    m = 7
    irrm = collect(irreducibles(Z[:x], m))
    f = prod(irrn[2:4]) * prod(irrm[3:4]) * irrn[2]
    @test isreducible(f)
    ff = factor(f)
    @test length(ff) == 5
    @test prod(ff) == f

    @test length(irrn) == necklace(p, n)
    @test length(irrm) == necklace(p, m)

    redn = collect(reducibles(Z[:x], n))
    @test length(redn) + length(irrn) == p^n
end

@testset "factor non-monic" begin
    Z = ZZ/3
    x = monom(Z[:x])
    p = (-x+1)^9
    @test prod(factor(p)) == p
    p = zero(p)
    @test factor(p) == [p => 1]
    p = one(p)
    @test factor(p) == [p => 1]
    p = x + 1
    @test factor(p) == [p => 1]
    p = -x + 1
    @test factor(p) == [-one(x) => 1, x - 1 => 1]
    p = -(x+1)^3
    @test factor(p) == [-one(x) => 1, x + 1 => 3]
end

