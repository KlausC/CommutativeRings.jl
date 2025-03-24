module TestFastMultiply

using CommutativeRings
using CommutativeRings: schoenhage_strassen

using Test

@testset "schoenhage_strassen 1" begin
    F = [1]
    G = [1]
    H = [1]
    @test schoenhage_strassen(F, G, 0) == H
end

@testset "schoenhage_strassen $N" for N in (8, 16, 32, 64)
    F = rand(-100:100, N)
    P = ZZ{Int}[:x]
    Q = P / (monom(P, N) + 1)
    p = P(F)^2
    F2 = schoenhage_strassen(F, F, 2N)
    n2 = length(F2)
    @test n2 <= 2N - 1
    @test p[0:n2-1] == F2
    q = Q(p)
    FN = schoenhage_strassen(F, F, N)
    nn = length(FN)
    @test nn <= N
    @test value(q)[0:nn-1] == FN
end

end
