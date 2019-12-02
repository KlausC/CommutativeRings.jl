

@testset "construction" begin
    P = ZZ{Int}[:x,:y,:z]
    x, y, z = generators(P)
    @test Ideal(x, y) isa Ideal
end
