module ResultantTest

using Test
using CommutativeRings

x = monom(ZZ{BigInt}[:x])
@testset "resultant($a,$b)" for (a, b, c) in (
    (0, 0, 0),
    (0, 1, 0),
    (0, x, 0),
    (3, 0, 0),
    (3, 2, 1),
    (3, x, 3),
    (3, 5x^2 + 1, 3^2),
    (7, 5x^7 - 1, 7^7),
    (2x^32 + 1, 3 * x^11 + 13, 906811932214969750127235270540901107329),
    (2x^31 + 1, 3x^11 + 1, -617673396281899),
)

    @test resultant(a, b) == c
    @test resultant(b, a) == c * (-1)^(deg(a) * deg(b) + 2)
    @test resultant(11a, 13b) == (a * b == 0 ? 0 : c * big(11)^deg(b) * big(13)^deg(a))

    ref = CommutativeRings.resultant_naive
    @test a * b == 0 || ref(a * x^0, b * x^0) == c
    @test a * b == 0 || ref(b * x^0, a * x^0) == c * (-1)^(deg(a) * deg(b) + 2)
end

@testset "discriminant" begin
    x = monom(ZZ{BigInt}[:x])
    @test discriminant(5x^2 + 10x + 2) == 60
    @test discriminant(3x^3 + x^2 + 4x + 10) == -22932
end

@testset "pgcdx" begin
    P = ZZ{BigInt}[:x]
    x = monom(P)
    A = x^2 + 2x + 1
    B = x + 1
    @test pgcdx(A, B) == (x + 1, 0, 1, 1)
    @test pgcdx(2A, 2B) == (2x + 2, 0, 1, 1)
end

end # module
