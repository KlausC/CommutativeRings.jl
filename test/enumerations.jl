
using CommutativeRings: len, GFImpl

@testset "iterate" begin
    @test length(collect(ZZ/7)) == 7
    @test length(collect(GF(3,5))) == 3^5
    @test length(collect(Monic((ZZ/2)[:x], 5))) == 2^5
    @test eltype(Monic((ZZ/2)[:x], 5)) == (ZZ/2)[:x]
end


@testset "ofindex $T" for (T, r) in ((Int, 0), (UInt, 0), (ZZ{Int8}, 0), (ZZ/77, 77), (GF(2,5),2^5), (QQ{Int}, 0))
    @test iszero(ofindex(0, T))
    @test isone(ofindex(1, T))
    @test ofindex(10, T) isa T
    @test len(T) == r
end

@testset "ofindex $T degree $n" for (T, n) in ((GF(2)[:z], 3),)
    @test ofindex(0, T, n) == monom(T, n)
    @test ofindex(1, T, n) == monom(T, n) + 1
    @test ofindex(10, T, n) isa T
end

@testset "ofindex Quotient" begin
    P = (ZZ/5)[:x]
    x = monom(P)
    Q = P / ( x^3 + x + 1)
    n = length(Q)
    @test length(Q) == 125
    @test sort(ofindex.(0:n-1, Ref(Q))) == sort(collect(Q))
end

@testset "factors" begin
    @test length(factors(12)) == 6
    @test factors(12) |> collect |> sort == [1, 2, 3, 4, 6, 12]
end

function fullset(n, k)
    n == 0 && return [Int[]]
    res = Vector{Int}[]
    for s in fullset(n-1, k)
        for e in -k:k
            cs = copy(s)
            push!(cs, e)
            push!(res, cs)
        end
    end
    Set(res)
end

using CommutativeRings: select_n_tuple

@testset "enumerate Z^$n - $k" for n = 1:5, k = 1:2
    @test Set(select_n_tuple.(1:(2k+1)^n, n)) == fullset(n, k)
end

import CommutativeRings: row2index, index2row, index2indexdegree, indexdegree2index, row2degree, degree2row

@testset "enumerate polynomials" begin
    @test row2index(0) == 0
    @test index2row(0) == 0
    @test index2indexdegree(0) == (0, 0)
    @test indexdegree2index(0, 0) == 0
    n = big(10)<<100
    @test indexdegree2index(index2indexdegree(n)...) == n
    n = typemax(UInt)
    @test indexdegree2index(index2indexdegree(n)...) == n
end
@testset "enumeration basics type $T" for T in (UInt8, Int8, UInt16, Int16, UInt32, Int32, UInt64, Int64, UInt128, Int128, BigInt)
    @test row2degree(zero(T)) == 0
    @test row2degree(one(T)) == 1
    @test row2degree(T(2)) == 1
    if T != BigInt
        @test row2degree(typemax(T)) == row2degree(big(typemax(T)))
    end
end
