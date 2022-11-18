module PowerSeriesTest

using Test
using CommutativeRings

@testset "construction" begin
    R = QQ{BigInt}
    x = monom(R[:x])
    P = PowerSeries{12}
    s = P(1 + 2x + 3x^13)
    @test typeof(s) == PowerSeries{R,:x,12}
    @test precision(typeof(s)) == precision(s) == 12
    t = P(x^12+x^25)
    @test precision(t) == 12
    @test precision(t /  x^10) == 12
    @test ord(t / x^15) == -3
end

end # module
