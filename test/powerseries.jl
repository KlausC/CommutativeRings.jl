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
sx = monom(S)
ex = sum(sx^k / factorial(k) for k = 0:PR)

@testset "construction" begin
    @test P{R,X} == S
    @test S == PowerSeries{PR,R,X}
    @test precision(typeof(s)) == precision(s) == PR
    @test precision(t) == PR
    @test precision(t / x^10) == PR
    @test ord(t / x^15) == -3
    @test PowerSeries{-1,R,X}(zero(S)) isa PowerSeries{-1,R,X}
    @test PowerSeries{10,R,X} == R[[:x], 10]
end

@testset "basic operations" begin
    @test t ≈ copy(t)
    @test copy(t) != t
    @test iszero(zero(S))
    @test one(S) isa S
    @test isunit(t)
    @test !isunit(zero(S))
    @test t[12] == 1
    @test t[[0, 12, 25]] == [0, 1, 0]
    @test s[0:PR] == [1; 2; zeros(Int, PR - 1)]
end

@testset "evaluation" begin
    @test t(x^2) isa S
    @test t(t) isa S
    @test (x^2)(t) ≈ t * t
    @test t(1) == t.poly(1)
    @test precision(t(x)) == precision(t)
end

@testset "arithmetic operations" begin
    s = S(1 - x)
    @test +s == s
    @test -s + s == 0
    @test s^2 + t ≈ S(x^12 + x^2 - 2 * x + 1)
    @test s^2 + t != S(x^12 + x^2 - 2 * x + 1)
    @test inv(s) ≈ S(sum(x^k for k = 0:PR))
    ex = P(sum(x^k / factorial(k) for k = 0:PR))
    emx = P(sum((-x)^k / factorial(k) for k = 0:PR))
    @test 1 / ex != emx
    @test 1 / ex ≈ emx
    @test precision(emx) == PR
    @test precision(emx - 1) == PR - 1
    v = S(1 + x^(PR - 1))
    @test PR < precision(v * v) <= PR + 10 + 1
end

@testset "composition inverse" begin
    exm1 = P(sum(x^k / factorial(k) for k = 1:PR))
    lg = P(sum(-(-x)^k / k for k = 1:PR))
    @test compose_inv(exm1) ≈ lg
    @test compose_inv(exm1) != lg
    @test compose_inv(lg) ≈ exm1
    @test compose_inv(lg) != exm1
end

@testset "derive" begin
    emx = P(sum((-x)^k / factorial(k) for k = 0:PR))
    @test precision(derive(emx) + emx) == PR - 1
    @test emx' ≈ derive(emx)
    @test emx' != derive(emx)
end

@testset "show cases" begin
    @test sprint(show, zero(S)) == "0"
    @test sprint(show, x) == "x"
    @test sprint(show, s) == "1 + 2*x + O(x^13)"
    @test sprint(show, s - s) == "O(x^13)"
end

@testset "O-terms" begin
    @test O(x^20) isa PowerSeries{-1,R,X}
    @test_throws ArgumentError x + O(x^20)
    @test s - O(x^20) isa PowerSeries{PR,R,X}
    @test sx + O(x) ≈ O(x)
    @test sx + O(x) != O(x)
    @test x + O(sx^2) ≈ sx + O(x^2)
    @test x + O(sx^2) != sx + O(x^2)
    @test sx + O(x^0) ≈ O(x^0)
    @test sx + O(x^0) != O(x^0)
    @test x + O(sx) ≈ O(x)
    @test x + O(sx) != O(x)
    @test x^10 * O(sx^12) ≈ O(x^22)
    @test x^10 * O(sx^12) != O(x^22)
    @test O(x^2) / sx ≈ O(x)
    @test O(x^2) / sx != O(x)
    @test (S(x^16) + O(x^31))^2 ≈ sx^32 + O(x^48)
    @test (S(x^16) + O(x^31))^2 != sx^32 + O(x^48)
    @test (S(1 + x^8) + O(x^17))^2 ≈ 1 + 2 * x^8 + O(sx^16)
    @test (S(1 + x^8) + O(x^17))^2 != 1 + 2 * x^8 + O(sx^16)
    @test O(sx^10) * O(x^11) ≈ O(sx^21)
    @test O(sx^10) * O(x^11) != O(sx^21)
    @test O(sx^10) * sx ≈ O(sx^11)
    @test O(sx^10) * sx != O(sx^11)
    @test sx^-3 * O(x^10) ≈ O(x^7)
    @test sx^-3 * O(x^10) != O(x^7)
    @test zero(x) + O(x^12) isa PowerSeries{-1}
    @test precision(sx * 0) == precision(sx)
    @test O(x^12) ≈ 0
    @test 0 // 1 ≈ O(x^12)
    @test O(x^12) != 0
end

@testset "sqrt" begin
    z = sx
    p = 1 + z
    @test_throws ArgumentError sqrt(z)
    @test sqrt(1 + z)^2 ≈ 1 + z
    @test sqrt(1 + z)^2 != 1 + z
    @test sqrt(1 + 2z + z^2) == 1 + z
    @test precision(sqrt(1 + 2z^((PR-1)÷2) + z^(PR-1))) == precision(z)
    @test sqrt(ex) ≈ ex(z / 2)
    @test sqrt(ex) != ex(z / 2)
    @test precision(sqrt(ex)) == precision(ex)
    @test sqrt(z^2 * (1 - 2z + z^2)) == z * (1 - z)
end

end # module
