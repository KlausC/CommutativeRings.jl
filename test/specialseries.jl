module SpecialSeriesTest

using CommutativeRings
using CommutativeRings.SpecialPowerSeries
using Test

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

end # module
