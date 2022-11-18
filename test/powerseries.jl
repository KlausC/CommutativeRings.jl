module PowerSeriesTest

using Test
using CommutativeRings

R = QQ{BigInt}
x = monom(R[:x])
P = PowerSeries{12}
s = P(1 + 2x + 3x^13)
t = P(x^12 + x^25)
S = typeof(s)

@testset "construction" begin
    @test S == PowerSeries{R,:x,12}
    @test precision(typeof(s)) == precision(s) == 12
    @test precision(t) == 12
    @test precision(t / x^10) == 12
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
    @test s^2 + t == S(x^12 + x^2 - 2*x + 1)
    @test inv(s) == S(sum(x^k for k = 0:13))
    ex = P(sum(x^k / factorial(k) for k = 0:13))
    emx = P(sum((-x)^k / factorial(k) for k = 0:13))
    @test 1 / ex == emx
    @test precision(emx) == 12
    @test precision(emx - 1) == 11
end

@testset "composition inverse" begin
    emx = P(sum((-x)^k / factorial(k) for k = 0:13))
    lg = P(sum(x^k / k for k = 1:12))
    @test compose_inv(1-emx) == lg
end

end # module
