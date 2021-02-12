
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

@testset "degrees" begin
    @test deg(0) == -1
    @test deg(1) == 0
    @test deg(ZZ(0)) == -1
    @test deg(ZZ(10)) == 0
end

@testset "testrules $R" for R in (ZZ/25, GF(25))
    io = IOBuffer()
    @test sprint(CommutativeRings.testrules, R) == ""
end

@testset "basetypes($G)" for G in (Int, ZZ{Int}, ZZ/2, (ZZ/3)[:x], GF(2,2))
    @test length(basetypes(G)) == depth(G) + 1
end
