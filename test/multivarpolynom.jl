
using CommutativeRings
import CommutativeRings: ord2expo, expo2ord, cbin, varnames

const Z = ZZ{Int}

@testset "index calculations" begin
    
    @test_throws ArgumentError cbin(0, 0)
    @test cbin(0, 1) == (0, 0)
    @test cbin(10, 1) == (10, 10)
    @test cbin(10, 9) == (10, 10)
    @test cbin(100, 9) == (11, 55)

    @test_throws ArgumentError ord2expo(0, 1) == [7654320]
    @test ord2expo(7654321, 1) == [7654320]
    @test expo2ord([1234]) == 1235
    @test ord2expo(1, 3) == [0, 0, 0]
    @test expo2ord([0,0,0,0]) == 1
    @test ord2expo(binomial(20+4-1, 4)+1, 4) == [0,0,0,20]
    @test expo2ord([0,0,10]) == binomial(10 + 3 - 1, 3)+1

    @test expo2ord.(ord2expo.(1:10000, 2)) == 1:10000
    @test expo2ord.(ord2expo.(1:10000, 5)) == 1:10000
end

@testset "constructors" begin

    @test Z[] == Vector{Z}(undef, 0)
    @test Z[:x] <: UnivariatePolynomial
    @test Z[:x, :y] <: MultivariatePolynomial
    @test Z[[:x],[:y]] <: MultivariatePolynomial
end

@testset "varnames and generators" for P in (Z[:x, :y, :z], Z[[:x], [:y,:z]])
    x, y, z = monom.(P, [[1,0,0], [0,1,0], [0,0,1]])
    @test [x, y, z] == generators(P)
    @test varnames(P) == [:x, :y, :z]
    @test varnames(P(0)) == [:x, :y, :z]

    p = 3x^3*y + 4x^2*y^2 + 5x*y*z^2
    @test deg(p) == 4
    @test multideg(p) == [3,1,0]
    @test LC(p) == 3
    @test LM(p) == x^3*y
    @test LT(p) == 3*x^3*y
end

@testset "addition" for P in (Z[:x, :y], Z[[:x], [:y]])
    
    @test zero(P) + one(P) == one(P) 
    @test one(P) + one(P) == 2*one(P)
    @test -one(P) + one(P) == zero(P)
    @test -one(P) == (-1) * one(P)
    @test one(P) - one(P) == zero(P)

    x, y = generators(P)
    a = 4*x^3 + 3
    b = y + 5*x^3
    @test 5a - 4b == -4y + 15
    @test a + b == 5*x^3 + 5*y + 3
    @test deg(zero(P)) == -1
    @test deg(one(P)) == 0
    @test deg(x + 1) == 1
    @test deg(x*y + 1) == 2
end

@testset "multiplication" for P in (Z[:x, :y], Z[[:x], [:y]])

    @test zero(P) * zero(P) == zero(P)
    @test zero(P) * one(P) == zero(P)
    @test one(P) * one(P) == one(P)
    x, y = generators(P)
    @test 0*x == zero(P)
    @test x*1 === x
    @test (x + y)^2 == x^2 + 2x*y + y^2
    @test (x + y) * (x - y) == x^2 - y^2
    xy = x * 5 + 2y^2 + x*y
    @test one(P) * xy == xy
    @test xy * zero(P) == zero(P)
    @test xy^2 == 25x^2 + x^2*y*10 + 20x*y^2 + x^2*y^2 + 4x*y^3 + 4y^4
    @test xy * x == 5x^2 + 2x*y^2 + x^2*y 

    R = (ZZ/12)[:x,:y]
    xr = monom(R, [1, 0])
    @test (xr*3) * 4 == zero(R)
end

@testset "division" begin
    P = ZZ{BigInt}[:x, :y]
    x, y = generators(P)
    f = x^2 - y
    g = x^3 - x
    G = [f, g]
    h = f * (x^2+y^2) + g * (x + y) + 1
    a, r, d = pdivrem(h, G)
    @test d == 1
    @test sum(a .* G) + r == h
end

@testset "Gröbner base" for P in (Z[:x, :y], Z[[:x], [:y]])
    x, y = generators(P)
    @test groebnerbase([x, x]) == [x]
    @test hash(0*x) == hash(0)
    @test hash(x^0) == hash(1)
    f = x^2 - y
    g = x^3 - x
    @test groebnerbase([f, g]) == [x^2 - y, x*y - x, y^2 - y]
end

@testset "blocked order" begin
    P = Z[[:t], [:x,:y]]
    t, x, y = generators(P)
    @test (t + 1)^2 == t^2 + 2*t + 1
    @test (y + 1)^2 == y^2 + 2*y + 1
    @test (x + t)^2 == x^2 + 2*x*t + t^2
    @test (x+y)(1, 2, 3) == 5
    @test (t*x^2*y^3 + 1)(1, 2, 3) == 1*4*27 + 1
end

@testset "conversions" for P in (Z[:t, :x, :y], Z[[:t], [:x,:y]])
    t, x, y = generators(P)
    @test generators(P) == [t, x, y]

    Q = Z[:x]
    xq = monom(Q)
    @test P(0*xq) isa P
    @test P(0*xq) == zero(P)
    @test P(5*xq^0) == 5
    @test P(xq) == monom(P, [0, 1, 0])

    R = Z[:z]
    zr = monom(R)
    @test P(0*zr) isa P
    @test P(0*zr) == zero(P)
    @test P(5*zr^0) == 5
    @test_throws ArgumentError P(zr)

    Q = Z[:y, :x]
    yq, xq = monom(Q, [1,0]), monom(Q, [0,1])
    @test P(0*xq) isa P
    @test P(0*yq) == zero(P)
    @test P(5*xq^0) == 5
    @test P(xq) == monom(P, [0, 1, 0])
    @test P(xq + yq*xq) == x + y*x

    Q = Z[:z, :y, :x]
    zq, yq, xq = monom(Q, [1,0,0]), monom(Q, [0,1,0]), monom(Q, [0,0,1])
    @test P(0*xq) isa P
    @test P(0*yq) == zero(P)
    @test P(5*xq^0) == 5
    @test P(xq) == monom(P, [0, 1, 0])
    @test P(xq + yq*xq) == x + y*x
    @test_throws ArgumentError P(zq + xq + yq)
end

@testset "extension and elimination" begin
    P = Z[:x, :y]
    x, y = generators(P)
    Q = lextend(P, :t)
    ida = Ideal(x^2-y^2, y^3-2x*y-y^2+2x, x*y^2-3x*y+2x)
    idb = Ideal(x*y)
    t, = generators(Q)

    idc = Ideal([Q.(ida.base) .* (1 - t); Q.(idb.base) .* t])

end

