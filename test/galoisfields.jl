
using Random
using LinearAlgebra


let rng = MersenneTwister(1), x
mat(p::Integer, n::Integer) = rand(rng, 0:p-1, n, n)

@testset "Galois Fields" begin
    
    @test GF(7) <: ZZmod{7}
    @test GF(3) == GF(3,1)
    @test GF(5,3) <: Quotient{X,<:UnivariatePolynomial{:γ,<:ZZmod{5}}} where X
    
    G7 = GF(7)
    @test G7(3)^2 == G7(2)

    G53 = GF(5,3)
    @test inv(G53([1,0,1])) * G53([1,0,1]) == 1
   
    x = monom(basetype(G53), 1)
    ma53(p, n, k) = Matrix{G53}(mat(p, n) .* x^k)
    A = ma53(4, 3, 0) + ma53(4, 3, 1) + ma53(4, 3, 2)
    @test inv(A) * A == I

    io = IOBuffer()
    show(io, GF(5,3)([1,2,3]))
    s = String(take!(io))
    @test s == "{3:2:1%5}"
end
end
