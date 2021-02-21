
@testset "integer polynomials over $T" for T in (Int64, BigInt)
    P = ZZ{T}[:x]
    x = monom(P)
    a = x^2 + 5x + 1
    b = x + 2
    c = a * b
    @test factor(c) == [a =>1; b=>1]
end
