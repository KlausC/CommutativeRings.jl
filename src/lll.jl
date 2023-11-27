# Implementation of the LLL () algorithm.
# Franklin T. Luk, Daniel M. Tracy: An improved LLL algorithm (https://www.sciencedirect.com)
#

function lll_reduce(B::AbstractMatrix{T}, δ = 0.99, η = 0.51) where T<:Number
    0.25 < δ < 1 || throw(ArgumentError("need δ in (0.25,1), but was $δ"))
    0.25 <= η^2 < δ || throw(ArgumentError("need η in (0.5,$(sqrt(δ)), but was $η"))
    n, m = size(B)

    Q, R = qr(B)
    D = Diagonal(sign.(diag(R)))
    R = D * R
    Q = Matrix(Q) * D

    inttype(::Type{T}) where T = typeof(Integer(one(T)))
    MType = T <: Complex ? Complex{inttype(real(T))} : inttype(T)
    M = Matrix((MType(one(T)) * I)(m))
    k = 2
    while k <= m
        l = max(k - 1, 1) # in 1:k - 1
        for i = k-1:-1:l
            rii = abs2(real(R[i,i])) * η ^ 2
            if rii < abs2(real(R[i, k])) || rii < abs2(imag(R[i, k]))
                decrease!(R, M, i, k)
                #println("($i,$k) decrease1 $(inorm(B * M, 1))")
                #display(M)
            end
        end
        if abs2(R[k, k]) + abs2(R[k-1, k]) < δ * abs2(R[k-1, k-1]) # note: typo in paper
            swap!(R, M, Q, k, B)
            #println("($(k-1),$k)      swap $(inorm(B * M, 1))")
            #display(M)
            k = max(2, k - 1)
        else
            for i = l-1:-1:1
                rii = abs2(real(R[i,i])) * η ^ 2
                if rii < abs2(real(R[i, k])) || rii < abs2(imag(R[i, k]))
                    decrease!(R, M, i, k)
                    #println("($i,$k) decrease2 $(inorm(B * M, 1))")
                    #display(M)
                end
            end
            k += 1
        end
    end
    Q, R, M
end

inorm(B, a...) = sum(abs2.(B))

function decrease!(R, M, i, j)
    m = size(M, 1)
    γ = round(R[i, j] / R[i, i])
    R[1:i, j] .-= R[1:i, i] * γ
    M[1:m, j] .-= M[1:m, i] * eltype(M)(γ)
    nothing
end

function swap!(R, M, Q, i, B)
    n, m = size(Q, 1), size(R, 2)
    swapcols!(R, i - 1, i, 1:i)
    swapcols!(M, i - 1, i, 1:m)
    a, b = R[i-1:i, i-1]
    h = hypot(a, b)
    c, s = a / h, b / h
    R[i-1, i-1] = h
    R[i, i-1] = 0
    for k = i:m
        a, b = R[i-1:i, k]
        R[i-1, k] = a * c' + b * s'
        R[i, k] = a * s - b * c
    end
    for k = 1:n
        a, b = Q[k, i-1:i]
        Q[k, i-1] = a * c + b * s
        Q[k, i] = a * s' - b * c'
    end
end

function swapcols!(R, i, j, r)
    for k in r
        R[k, i], R[k, j] = R[k, j], R[k, i]
    end
end

#=
INPUT
    a lattice basis b1, b2, ..., bn in Zm
    a parameter δ with 1/4 < δ < 1, most commonly δ = 3/4
PROCEDURE
    B* <- GramSchmidt({b1, ..., bn}) = {b1*, ..., bn*};  and do not normalize
    μi,j <- InnerProduct(bi, bj*)/InnerProduct(bj*, bj*);   using the most current values of bi and bj*
    k <- 2;
    while k <= n do
        for j from k−1 to 1 do
            if |μk,j| > 1/2 then
                bk <- bk − ⌊μk,j⌉bj;
               Update B* and the related μi,j's as needed.
               (The naive method is to recompute B* whenever bi changes:
                B* <- GramSchmidt({b1, ..., bn}) = {b1*, ..., bn*})
            end if
        end for
        if InnerProduct(bk*, bk*) > (δ − μ2k,k−1) InnerProduct(bk−1*, bk−1*) then
            k <- k + 1;
        else
            Swap bk and  bk−1;
            Update B* and the related μi,j's as needed.
            k <- max(k−1, 2);
        end if
    end while
    return B the LLL reduced basis of {b1, ..., bn}
OUTPUT
    the reduced basis b1, b2, ..., bn in Zm
=#

"""
    algebraic_relationship(a; e=1e-5, c=1e9)

Given a vector of numbers `a`, find small integers `m` such that `m' * a` is small.
The constant `c` is used to set up the initial matrix to be `lll_reduce`d.

"""
function algebraic_relationship(a::Vector{<:Number}; e::AbstractFloat=1e-5, c::Number=1e9)
    B = [c * a'; I]
    Q, R, M = lll_reduce(B)
    m = M[:,1]
    d = abs(m'a)
    d > e && throw(ArgumentError("no convergence"))
    m
end

function minimal_polynomial(a::Number, n::Integer;)
    m = algebraic_relationship([a^i for i = 0:n]; e, c)
    ZZ{Int}[:x](m)
end

export lll_reduce, algebraic_relationship
