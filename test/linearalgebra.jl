
using LinearAlgebra

const companion = CommutativeRings.companion

@testset "vector spaces" begin
    
    Z = ZZ/7

    xnull = VectorSpace(Matrix{Z}(undef, 5, 0))
    xall = VectorSpace(diagm(ones(Z, 5)))
    @test intersect(xnull, xnull) == xnull
    @test intersect(xnull, xall) == xnull
    @test intersect(xall, xall) == xall
    @test sum(xnull, xnull) == xnull
    @test sum(xall, xnull) == xall
    @test sum(xall, xall) == xall

    va = VectorSpace(Z[1 0; 0 1; 0 0; 0 0; 0 0])
    vb = VectorSpace(Z[0 0; 0 0; 0 0; 0 1; 1 0])

    vc = sum(va, vb)
    @test Matrix(vc) == [1 0 0 0; 0 1 0 0; 0 0 0 0; 0 0 0 1; 0 0 1 0]

    vc = intersect(va, vb)
    @test Matrix(vc) == Matrix{Z}(undef,5,0)

    vc = complement(vb)
    @test Matrix(vc) == Z[0 0 1; 0 1 0; 1 0 0; 0 0 0; 0 0 0]

    wa = VectorSpace(Z[1, 2, 3, 4, 5])
    wb = VectorSpace(Z[1, 2, 4, 4, 0])
    wc = VectorSpace(Z[0, 0, 2, 1, 0])
    xa = sum(wa, wc)
    xb = sum(wb, wc)

    @test intersect(wa, xa) == wa
    @test intersect(xa, wc) == wc
    @test intersect(wc, xb) == wc
    @test intersect(xb, wb) == wb

    xint = intersect(xa, xb)
    @test xint == wc

    xsum = sum(xa, xb)
    @test issubset(wa, xsum)
    @test issubset(wb, xsum)
    @test issubset(wc, xsum)
    @test issubset(xa, xsum)
    @test issubset(xb, xsum)

    @test intersect(xnull, xsum) == xnull
    @test intersect(xall, xsum) == xsum
    @test sum(xnull, xsum) == xsum
    @test sum(xall, xsum) == xall
end

@testset "determinant" begin
    G = ZZ/89
    A = G.([1 2 3; 4 5 6; 7 8 9])
    B = G.([1 2 3; 4 5 6; 7 8 8])
    @test iszero(det(A))
    @test iszero(adjugate(A) * A)
    @test !iszero(det(B))
    @test adjugate(B) ./ det(B) == inv(B)

    p = characteristic_polynomial(B)
    @test iszero(p(B))
    @test characteristic_polynomial(companion(p)) == p
end
