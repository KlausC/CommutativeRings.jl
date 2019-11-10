

@testset "irreducibles $p" for p = (2, 3)
    Z = ZZ/p
    n = 5
    irrn = collect(irreducibles(Z[:x], n))
    @test irreducible(Z[:x], n) == irrn[1]
    @test length(irrn) == necklace(p, n)
    m = 7
    irrm = collect(irreducibles(Z[:x], m))
    f = prod(irrn[2:4]) * prod(irrm[3:4]) * irrn[2]
    @test !isirreducible(f)
    ff = factor(f)
    @test length(ff) == 5
    @test prod(ff) == f

    @test length(irrn) == necklace(p, n)
    @test length(irrm) == necklace(p, m)
end

