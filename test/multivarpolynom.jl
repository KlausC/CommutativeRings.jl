
using CommutativeRings
import CommutativeRings: index2tuple, tuple2index, cbin, gettypevar

@testset "index calculations" begin
    
    @test_throws ArgumentError cbin(0, 0)
    @test cbin(0, 1) == (0, 0)
    @test cbin(10, 1) == (10, 10)
    @test cbin(10, 9) == (10, 10)
    @test cbin(100, 9) == (11, 55)

    @test_throws ArgumentError index2tuple(0, 1) == [7654320]
    @test index2tuple(7654321, 1) == [7654320]
    @test tuple2index([1234]) == 1235
    @test index2tuple(1, 3) == [0, 0, 0]
    @test tuple2index([0,0,0,0]) == 1
    @test index2tuple(binomial(20+4-1, 4)+1, 4) == [0,0,0,20]
    @test tuple2index([0,0,10]) == binomial(10 + 3 - 1, 3)+1

    @test tuple2index.(index2tuple.(1:10000, 2)) == 1:10000
    @test tuple2index.(index2tuple.(1:10000, 5)) == 1:10000
end

@testset "constructors" begin

    Z = ZZ{Int}
    @test Z[] == Vector{Z}(undef, 0)
    @test Z[:x] <: UnivariatePolynomial
    @test Z[:x, :y] <: MultivariatePolynomial
    P = Z[:x,:y,:z]
    @test gettypevar(P).varnames == [:x, :y, :z]
end

@testset "addition" begin
    
    Z = ZZ{Int}
    P = Z[:x, :y]
    @test zero(P) == P(Int[], Z[])
    @test one(P) == P([1], Z[1])
    @test zero(P) + one(P) == one(P) 
    @test one(P) + one(P) == 2*one(P)
    @test -one(P) + one(P) == zero(P)
    @test -one(P) == (-1) * one(P)
    @test one(P) - one(P) == zero(P)

    a = P([1,10], Z[3, 4])
    b = P([10], Z[5])
    @test a + b == P([1,10], Z[3, 9])
    @test 5a - 4b == P([1], Z[5])
end

@testset "multiplication" begin

    Z = ZZ{BigInt}
    P = Z[:x, :y]

    @test zero(P) * zero(P) == zero(P)
    @test zero(P) * one(P) == zero(P)
    @test one(P) * one(P) == one(P)
    x = P([3], [1])
    y = P([2], [1])
    @test (x + y)^2 == x^2 + 2x*y + y^2
    @test (x + y) * (x - y) == x^2 - y^2
    xy = x * 5 + 2y^2 + x*y
    @test one(P) * xy == xy
    @test xy * zero(P) == zero(P)
    @test xy^2 == 25x^2 + x^2*y*10 + 20x*y^2 + x^2*y^2 + 4x*y^3 + 4y^4
    @test xy * x == 5x^2 + 2x*y^2 + x^2*y 
end

@testset "division" begin
    P = ZZ{Int}[:x, :y]
    x = monom(P, [1, 0])
    y = monom(P, [0, 1])
    f = x^2 - y
    g = x^3 - x
    G = [f, g]
    h = f * (x^2+y^2) + g * (x + y) + 1
    r, a, d = red(h, G)
    @test d == 1
    @test sum(a .* G) + r == h
end

@testset "Gröbner base" begin
    P = ZZ{Int}[:x, :y]
    x = monom(P, [1, 0])
    y = monom(P, [0, 1])
    f = x^2 - y
    g = x^3 - x
    @test groebnerbase([f, g]) == [x^2 - y, x*y - x, y^2 - y]
end
