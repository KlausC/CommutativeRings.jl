module PowerSeriesTest

using Test
using CommutativeRings
using CommutativeRings: InfPrecision

R = QQ{BigInt}
X = :x
x = monom(R[X])
PR = 13
P = PowerSeries{PR}
s = P(1 + 2x + 3x^PR)
t = P(x^12 + x^25)
S = typeof(s)
sx = S(x)

@testset "construction" begin
    @test S == PowerSeries{R,X,PR}
    @test precision(typeof(s)) == precision(s) == PR
    @test precision(t) == PR
    @test precision(t / x^10) == PR
    @test ord(t / x^15) == -3
end

@testset "basic operations" begin
    @test t == copy(t)
    @test copy(t) !== t
    @test iszero(zero(S))
    @test one(S) isa S
    @test isunit(t)
    @test !isunit(zero(S))
end

@testset "evaluation" begin
    @test t(x^2) isa S
    @test t(t) isa S
    @test (x^2)(t) == t * t
    @test t(1) == t.poly(1)
end

@testset "arithmetic operations" begin
    s = S(1 - x)
    @test +s == s
    @test -s + s == 0
    @test s^2 + t == S(x^12 + x^2 - 2 * x + 1)
    @test inv(s) == S(sum(x^k for k = 0:PR))
    ex = P(sum(x^k / factorial(k) for k = 0:PR))
    emx = P(sum((-x)^k / factorial(k) for k = 0:PR))
    @test 1 / ex == emx
    @test precision(emx) == PR
    @test precision(emx - 1) == PR - 1
end

@testset "composition inverse" begin
    exm1 = P(sum(x^k / factorial(k) for k = 1:PR))
    lg = P(sum(-(-x)^k / k for k = 1:PR))
    @test compose_inv(exm1) == lg
    @test compose_inv(lg) == exm1
end

@testset "derive" begin
    emx = P(sum((-x)^k / factorial(k) for k = 0:PR))
    @test precision(derive(emx) + emx) == PR - 1
end

@testset "show cases" begin
    @test sprint(show, zero(S)) == "0"
    @test sprint(show, x) == "x"
    @test sprint(show, s) == "1 + 2*x + O(x^13)"
    @test sprint(show, s - s) == "O(x^13)"
end

@testset "O-terms" begin
    @test O(x^20) isa PowerSeries{R,X,InfPrecision}
    @test x + O(x^20) isa PowerSeries{R,X,InfPrecision}
    @test s - O(x^20) isa PowerSeries{R,X,PR}
    @test x + O(x) == O(x)
    @test x + O(x^2) == sx + O(x^2)
    @test x + O(x^0) == O(x^0)
    @test x + O(x) == O(x)
    @test x^10 * O(x^12) == O(x^22)
    @test O(x^2) / x == O(x)
    @test (x^16 + O(x^31))^2 == x^32 + O(x^48)
    @test (S(1+x^8) + O(x^17))^2 == 1 + 2*x^8 + O(x^16)
end

end # module
