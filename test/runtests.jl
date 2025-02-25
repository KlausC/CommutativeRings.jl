using Test
using CommutativeRings

macro testsetif(args...)
    isempty(ARGS) || in(args[end-1], ARGS) || return :nothing
    quote
        @testset($(args...))
    end
end

@testsetif "Aqua" begin include("Aqua.jl") end

@testsetif "typevars" begin include("typevars.jl") end
@testsetif "generic" begin include("generic.jl") end
@testsetif "ZZ" begin include("zz.jl") end
@testsetif "QQ" begin include("qq.jl") end
@testsetif "ZZmod" begin include("zzmod.jl") end
@testsetif "galoisfields" begin include("galoisfields.jl") end
@testsetif "fraction" begin include("fraction.jl") end
@testsetif "quotient" begin include("quotient.jl") end
@testsetif "univarpoly" begin include("univarpolynom.jl") end
@testsetif "determinant" begin include("determinant.jl") end
@testsetif "resultant" begin include("resultant.jl") end
@testsetif "multivarpoly" begin include("multivarpolynom.jl") end
@testsetif "ideal" begin include("ideal.jl") end
@testsetif "factors" begin include("factorization.jl") end
@testsetif "numbertheory" begin include("numbertheoretical.jl") end
@testsetif "enumerations" begin include("enumerations.jl") end
@testsetif "linearalgebra" begin include("linearalgebra.jl") end
@testsetif "rationalnormal" begin include("rationalcanonical.jl") end
@testsetif "intfactors" begin include("intfactorization.jl") end
@testsetif "powerseries" begin include("powerseries.jl") end
@testsetif "specialseries" begin include("specialseries.jl") end
@testsetif "LLL" begin include("lll.jl") end
@testsetif "fourier" begin include("fourier.jl") end
@testsetif "fastMultiply" begin include("fastmultiply.jl") end
@testsetif "algebraic numbers" begin include("algebraic.jl") end
@testsetif "number fields" begin include("numberfield.jl") end
