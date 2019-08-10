
@testset "construction" begin
    P = UnivariatePolynomial{:x,ZZ{Int}}
    p = P([1, 2])
    q = P([1, 1])
    @test Frac(p, q) != nothing
    @test p // q == Frac(p, q)
    @test p // p == 1
end
