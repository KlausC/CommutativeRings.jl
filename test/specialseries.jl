module SpecialSeriesTest

using CommutativeRings
using CommutativeRings.SpecialPowerSeries
using Test

const Names = names(CommutativeRings.SpecialPowerSeries) ∩ names(Base.Math)
const Funcs = eval.(Names)

x = monom(QQ{BigInt}[[:x], 100])
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

end # module
