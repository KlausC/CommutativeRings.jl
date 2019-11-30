

@testset "construction" begin
    P = ZZ{Int}[:x,:y,:z]
    x, y, = monom(P, [1, 0]), monom(P, [0, 1])
    @test Ideal(x, y) <:Ideal
end
