module NumbertheoreticalTest

using Test
using CommutativeRings
using Primes

x = monom(QQ{Int}[:x], 1)
P = ZZ{Int}[:z]
z = monom(P)

@testset "cyclotomic" begin
    @test cyclotomic(P, 100) == z^40 - z^30 + z^20 - z^10 + 1
    @test deg(cyclotomic(P, 385)) == totient(385)

    # the following is true for all prime `p` and natural `n`
    # => factorization of `x^p^n - 1`
    p, n = 11, 3
    @test prod(cyclotomic.(P, p .^ (1:n))) * (z - 1) == z^p^n - 1
end

@testset "kronecker ($n, $k, $r)" for (n, k, r) in (
    (1, 1, 1),
    (1, 13, 1),
    (12, 1, 1),
    (5, 8, -1),
    (12, 18, 0),
    (6, 17, -1),
    (6, -17, -1),
    (-6, 17, -1),
    (-6, -17, 1),
)
    @test kronecker(n, k) == r
end

@testset "moebius ($n, $r)" for (n, r) in (
    (1, 1),
    (2, -1),
    (3, -1),
    (4, 0),
    (5, -1),
    (6, 1),
    (8, 0),
    (10, 1),
)
    @test moebius(n) == r
end

@testset "necklace ($n, $r)" for (n, r) in (
    (1, x),
    (2, (x^2 - x) / 2),
    (6, (x^6 - x^3 - x^2 + x) / 6),
)
    @test necklace(x, n) == r
    @test necklace(17, n) == r(17)
end

end # module
