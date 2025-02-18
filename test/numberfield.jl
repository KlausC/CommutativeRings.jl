module NumberFieldTests

using CommutativeRings
using Test

P = QQ{BigInt}[:x]
x = monom(P)
tol = eps(BigFloat) * 100
a = AlgebraicNumber(x^3 + x^2 - 1)
N = NF(a)
y = monom(N)

@testset "NumberField constructors" begin
    @test y isa NumberField
    @test N <: NumberField
    @test base(N) == a
    @test zero(y) == 0
    @test one(y) == 1
    @test monom(N, 2) == y^2
    @test generator(N) == y
    @test isunit(y)
    @test !isunit(zero(N))
end

@testset "NumberField hash" begin
    @test hash(one(N)) == hash(1)
    @test N(1//2) == one(N) / 2
    M = NF(AlgebraicNumber(x^3 + x^2 - 1, 1))
    @test M(1) == N(1)
    @test M != N
    @test monom(M) != monom(N)
    @test hash(M(x)) != hash(N(x))
end

@testset "NumberField $op operation" for op in (-, inv)
    u = N(x^2 - x + 12)
    @test op(u).repr == op(u.repr)
end

@testset "NumberField $op(.,.) operation" for op in (+, -, *, /)
    u = N(x^2 + 1)
    v = N(x^99)
    @test op(u, v).repr == op(u.repr, v.repr)
end

@testset "conversion to AlgebraicNumber" begin
    u = N(x^2 + x)
    b = AlgebraicNumber(u)
    @test minimal_polynomial(u)(u) == 0
    @test approx(u) ≈ approx(b)
    M = NF(b)
    v = monom(M)
    @test approx(v) ≈ approx(u)
end

@testset "show NumberField class and element" begin
    @test string(N(x)) isa String
    @test string(N) isa String
end

end
