
using CommutativeRings: hensel_lift, partsums, subset, remove_subset!, allgcdx

let x = monom(ZZ{Int}[:x]), u = x^8 + x^6 -3x^4 -3x^3 +8x^2 + 2x - 5

@testset "integer polynomials over $T" for T in (Int64, BigInt)
    x = monom(ZZ{T}[:x])
    b = x^2 + 5x + 1
    a = x + 2
    c = a * b
    @test factor(c) == [a =>1; b=>1]
end

@testset "coeffbounds" begin
    @test_throws ArgumentError coeffbounds(zero(u), 0)
    @test_throws ArgumentError coeffbounds(10one(u), 1)
    @test coeffbounds(10one(u), 0) == [10]
    @test coeffbounds(u, 0) == [1]
    @test coeffbounds(u, 1) == [5, 1]
    @test coeffbounds(u, 2) <= [5, 12, 1]
    @test coeffbounds(u, 3) <= [5, 21, 13, 1]
    @test coeffbounds(u, 4) <= [5, 26, 36, 14, 1]
end

@testset "hensel_lifting" for (p, q) in [(13, 13)]
    X = varname(x)
    
    r = gcd(p, q)
    Pq = (ZZ/q)[X]
    Pqr = (ZZ/(q*r))[X]
    v = first.(factor(Pq(u)))
    a = allgcdx(v)
    V, qr = hensel_lift(u, v, a)
    @test Pqr(u) == Pqr(prod(V))
    @test all(Pq.(V) .== v)

    #=
    p, q = p, q * r
    r = gcd(p, q)
    Pq = (ZZ/q)[X]
    Pqr = (ZZ/(q*r))[X]
    v = V
    V, qr = hensel_lift(u, v, a)
    @test Pqr(u) == prod(V)
    @test all(Pq.(V) .== v)
    =#
end

@testset "partsums" begin
    s = [2, 3, 10]
    @test partsums(s) == ( 0xb42d, [1,0,1,1,0,1,0,0], [[0], [], [1], [2], [], [3], [], []])


end

@testset "subsets" begin
    vv = [10, 20, 30, 40]
    @test subset(vv, 0) == Int[]
    @test subset(vv, 6) == [20, 30]
    @test subset(vv, -1) == vv

    @test remove_subset!(copy(vv), -1) |> isempty
    @test remove_subset!(copy(vv), 5) == [20, 40]
    remove_subset!(vv, 8)
    @test vv == [10, 20, 30]
end

end
