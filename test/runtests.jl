using Test
using CommutativeRings

@testset "Aqua" begin include("Aqua.jl") end

@testset "typevars" begin include("typevars.jl") end
@testset "generic" begin include("generic.jl") end
@testset "ZZ" begin include("zz.jl") end
@testset "QQ" begin include("qq.jl") end
@testset "ZZmod" begin include("zzmod.jl") end
@testset "galoisfields" begin include("galoisfields.jl") end
@testset "fraction" begin include("fraction.jl") end
@testset "quotient" begin include("quotient.jl") end
@testset "univarpoly" begin include("univarpolynom.jl") end
@testset "determinant" begin include("determinant.jl") end
@testset "resultant" begin include("resultant.jl") end
@testset "multivarpoly" begin include("multivarpolynom.jl") end
@testset "ideal" begin include("ideal.jl") end
@testset "factors" begin include("factorization.jl") end
@testset "numbertheory" begin include("numbertheoretical.jl") end
@testset "enumerations" begin include("enumerations.jl") end
@testset "linearalgebra" begin include("linearalgebra.jl") end
@testset "rationalnormal" begin include("rationalcanonical.jl") end
@testset "intfactors" begin include("intfactorization.jl") end
@testset "powerseries" begin include("powerseries.jl") end
@testset "specialseries" begin include("specialseries.jl") end
@testset "LLL" begin include("lll.jl") end
@testset "fourier" begin include("fourier.jl") end
@testset "fastMultiply" begin include("fastmultiply.jl") end
