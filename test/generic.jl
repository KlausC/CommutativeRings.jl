
import CommutativeRings: tosuper, tosub

@testset "scriptdigits" begin

    @test tosuper(0) == "⁰"
    @test tosuper(0, sign=true) == "⁺⁰"
    @test tosuper(1234) == "¹²³⁴"
    @test tosuper(1234, sign=true) == "⁺¹²³⁴"
    @test tosuper(-1234) == "⁻¹²³⁴"
    @test tosuper(-1234, sign=true) == "⁻¹²³⁴" 
    @test tosub(0) == "₀"
    @test tosub(0, sign=true) == "₊₀"
    @test tosub(1234) == "₁₂₃₄"
    @test tosub(1234, sign=true) == "₊₁₂₃₄" 
    @test tosub(-1234) == "₋₁₂₃₄"
    @test tosub(-1234, sign=true) == "₋₁₂₃₄"  

end
