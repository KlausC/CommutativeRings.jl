# Algorithms according to
# Algorithmes Efficaces en Calcul Formel
# Alin Bostan, Frédéric Chyzak, Marc Giusti, Romain Lebreton, Grégoire
# Lecerf, Bruno Salvy, Eric Schost
# https://inria.hal.science/hal-01431717/document Chap 6.3
# Chap 6.3 Algorithme d’Euclide rapide
# pp 131

"""
    halfgcd(A, B)

Given polynomials `A, B` with `deg(A) > deg(B)`
Return a 2x2 `M::Matix{P}` with `M * (A, B)'` with approximatly
degrees of `max(deg(A))) / 2`.
"""
#halfgcd(A::P, B::P) where P = halfgcd!(P[1 0;0 1], A, B)

function halfgcd(A::P, B::P) where {P<:UnivariatePolynomial}

    #println("halfgcd($(deg(A)), $(deg(B))), $(logsize(A)), $(logsize(B))")
    #println("halfgcd!($(maximum(deg.(MM))), $(logsize(MM)), $(deg(A)), $(deg(B)))")
    #println(content(A))
    #println(content(B))
    n = deg(A)
    nb = deg(B)
    m = (n + 1) ÷ 2
    if n <= nb || nb <= 0 || nb < m
        return P[1 0; 0 1]
    end
    xm = monom(P, m)
    f = div(A, xm)
    g = div(B, xm)
    M = halfgcd(f, g)
    A, B = M * [A; B]
    if deg(B) < m
        return M
    end
    #println("divremh($(deg(A)), $(deg(B)))")
    Q, C = divrem(A, B)
    multi!(M, Q)

    l = 2*m - deg(B)
    xl = monom(P, l)
    b = div(B, xl)
    c = div(C, xl)
    if iszero(c)
        return M
    end
    halfgcd(b, c) * M
end

function multi!(M, Q)
    M1, M2 = M[2,1:2]
    M[2,1] = M[1,1] - Q*M1
    M[2,2] = M[1,2] - Q*M2
    M[1,1] = M1
    M[1,2] = M2
    return
end

logsize(A::Polynomial) = log(maximum(abs.(value.(A.coeff)); init=0.0))
logsize(A::AbstractArray) = maximum(logsize.(A))

#fastgcd(A::P, B::P) where P = fastgcd!(P[1 0; 0 1], A, B)

#function fastgcd!(MM, A, B)
function fastgcd(A::P, B::P) where P
    if iszero(B)
        return P[1 0; 0 1]
    end
    M = halfgcd(A, B)
    R0, R1 = M * [A; B]
    if iszero(R1)
        return M
    end
    #println("divrem($(deg(R0)), $(deg(R1)))")
    Q, R2 = divrem(R0, R1)
    multi!(M, Q)
    if iszero(R2)
        return M
    end
    #println("fastgcd($(deg(R1)), $(deg(R2)))")
    fastgcd(R1, R2) * M
end

function euclid(A, B)
    R0, U0, V0 = A, one(A), zero(A)
    R1, U1, V1 = B, zero(B), one(B)

    while deg(R1) >= (deg(A) + 1) ÷ 2
        Q, R2 = divrem(R0, R1)
        U2 = U0 - Q * U1
        V2 = V0 - Q * V1
        u = LC(R2)
        R0, R1, U0, U1, V0, V1 = R1, R2 / u, U1, U2 / u, V1, V2 / u
        #println("U1 = $U1 V1 = $V1 R1 = $R1")
    end
    [U0 V0; U1 V1]
end
