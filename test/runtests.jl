using Test
using CommutativeRings

@testset "ZZ" begin include("zz.jl") end
@testset "ZZmod" begin include("zzmod.jl") end
@testset "univarpolynom" begin include("univarpolynom.jl") end


