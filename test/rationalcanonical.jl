
@testset "minimal_polynomial" begin
    Q = QQ{BigInt}
    A = Q.([-3 -1 4 -3 -1
       1 1 -1 1 0
       -1 0 2 0 0
       4 1 -4 5 1
       -1 0 1 -1 1])

    ma, xa = minimal_polynomial(A)
    ca = companion(ma)
    n = 4
    @test deg(ma) == n
    @test characteristic_polynomial(ca) == ma
    B = CommutativeRings.axspace(A, xa, n)
    @test A * B == B * ca
end
