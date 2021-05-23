
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

@testset "homomorphisms" begin
    R = ZZ/7
    S = GF(7, 2)
    h = Hom{R,S}(S)
    @test h(R(2)) == S(2)
end

@testset "isfield $F" for (F, r) in ((ZZ{Int}, false), (ZZ/6, false), (ZZ/3, true), (QQ{Int}, true), (ZZ{Int}[:x], false))
    @test isfield(F) == r
end

@testset "promotion1" begin
    P = QQ{Int}[:x]
    x = monom(P)
    Q = P / (x^2 - 2)
    @test x + 1//7 isa P
    @test 1//7 + x isa P
    @test Q(x) + 1 // 7 isa Q
    @test 1 // 7 + Q(x) isa Q
end

@testset "promotion2" begin
    P = ZZ{Int}[:x]
    x = monom(P)
    Q = P / ( x^2 - 3)
    PP = Q[:y]
    y = monom(PP)
    @test x * y == Q(x) * y
    @test Q(x) * y isa PP
end

@testset "promotion3" begin
    P = ZZ{Int}[:x]
    x = monom(P)
    R = P[:y]
    y = monom(R)
    S = R[:z]
    z = monom(S)
    @test z + x isa S
    @test (x + y + z)^2 == x^2 + y^2 + z^2 + 2x*y + 2x*z + 2y*z
    
end

using CommutativeRings: FieldTrait, EuclidianDomainTrait, UniqueFactorizationDomainTrait, IntegralDomainTrait, CommutativeRingTrait

@testset "category traits $T" for (T,C) in [(ZZ, EuclidianDomainTrait),
                                            (ZZ/2, FieldTrait),
                                            (GF(4), FieldTrait),
                                            (QQ{BigInt}, FieldTrait),
                                            (ZZ/6, CommutativeRingTrait),
                                            (ZZ{Int}[:x], UniqueFactorizationDomainTrait),
                                            (ZZ{Int}[:x][:y], UniqueFactorizationDomainTrait),
                                            (ZZ{Int}[:x,:y], UniqueFactorizationDomainTrait),
                                            ((ZZ/3)[:x], EuclidianDomainTrait),
                                            ((ZZ/3)[:x,:y], UniqueFactorizationDomainTrait)
                                          ]
    @test category_trait(T) == C
end

const X = monom(ZZ{Int}[:x])
@testset "category traits $T/($p)" for (T, p, C) in [(ZZ/5, X^2 + 2, FieldTrait),
                                                     (ZZ/5, X^2 + 1, CommutativeRingTrait),
                                                  ]                     
    x = monom(T[:x])
    P = p(x)
    @test category_trait(T[:x]/P) == C
end

@testset "category traits Frac{$T}" for (T, C) in [(ZZ{Int}, FieldTrait),
                                                   (ZZ{Int}[:x], FieldTrait),
                                                   ((ZZ/6)[:x], CommutativeRingTrait),
                                                  ]
    @test category_trait(Frac{T}) == C
end