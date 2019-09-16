
using Primes

@testset "cyclotomic" begin
    P = ZZ{Int}[:x]
    @test deg(cyclotomic(P, 385)) == totient(385)
end

