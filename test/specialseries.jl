module SpecialSeriesTest

using CommutativeRings
using CommutativeRings.SpecialPowerSeries
using Test
using LinearAlgebra

const Names = names(CommutativeRings.SpecialPowerSeries) ∩ names(Base.Math)
const Funcs = eval.(Names)

x = monom(QQ{BigInt}[[:x], 100])
z = monom(QQ{BigInt}[[:z], 20])

@testset "Base.Math function $fn" for (fn, f) in zip(Names, Funcs)
    fx = f(x)
    z = 0.1
    @test f(z) ≈ fx(z)
end

@testset "sqrt1p" begin
    fx = sqrt1p(x)
    z = 0.1
    @test sqrt(1 + z) ≈ fx(z)
end

@testset "versine" begin
    @test cos(x) ≈ 1 - ver(x)
end

@testset "log and pade" begin
    lg = log1p(z)
    plg = pade(lg, 10, 10)
    @test abs(lg(1.0) - log1p(1.0)) > 1e-2
    @test abs(plg(1.0) - log1p(1.0)) < 1e-10
end

@testset "Li Ei" begin
    lg = log1p(z)
    @test lin1pe(lg) ≈ lin1p(z)
    @test Li(z, 2)(1) == 17299975731542641 // 10838475198270720
end


@testset "Bernoulli and Euler numbers" begin

    @test B.(0:6) == [1, -1//2, 1//6, 0, -1//30, 0, 1//42]
    @test E.(0:6) == [1, 0, -1, 0, 5, 0, -61]

    @test B(200) ≈ -3.647077264519136e215
    @test E(180) ≈ 1.2773316636719806e294
end


@testset "podhammer-stirling" begin
    x = monom(ZZ{BigInt}[:x])

    @test podhammer(x, 5) == x^5 - 10x^4 + 35x^3 - 50x^2 + 24x
    @test podhammer(x + 4, 5) == (x+4)*(x+3)*(x+2)*(x+1)*x

    @test stirling1(0, 0) == 1
    @test stirling1.(7, 0:7) == [0, 720, -1764, 1624, -735, 175, -21, 1]
    @test stirling2(0, 0) == 1
    @test stirling2.(7, 0:7) == [0, 1, 63, 301, 350, 140, 21, 1]

    a1 = [stirling1(n, k) for n = 1:10, k = 1:10]
    a2 = [stirling2(n, k) for n = 1:10, k = 1:10]
    @test a1 * a2 == I

    @test sum(stirling2(11, k) * podhammer(x, k) for k = 0:11) == x^11
    @test sum(stirling1(11, k) * x^k for k = 0:11) == podhammer(x, 11)
    @test sum(stirling2r(11, k) * podhammer(x, -k) for k = 0:11) == x^11
    @test sum(stirling1r(11, k) * x^k for k = 0:11) == podhammer(x, -11)

    @test_throws OverflowError stirling1(1000, 500)
    @test_throws OverflowError stirling2(1000, 500)
    @test Float64(stirling1(big(1000), 950)) ≈ 5.270686807719337e219
    @test Float64(stirling2(big(1000), 950)) ≈ 9.866390699448044e218
end

end # module
