# Implementation of the LLL () algorithm.
# Franklin T. Luk, Daniel M. Tracy: An improved LLL algorithm (https://www.sciencedirect.com)
#

function lll_reduce(B::AbstractMatrix{T}, δ::Real = 0.99, η::Real = 0.51) where T<:Number
    lll_reduce!(copy(B), δ, η)
end
function lll_reduce!(B::AbstractMatrix{T}, δ::Real, η::Real) where T<:Number
    0.25 < δ < 1 || throw(ArgumentError("need δ in (0.25,1), but was $δ"))
    0.25 <= η^2 < δ || throw(ArgumentError("need η in (0.5,$(sqrt(δ)), but was $η"))
    call_repeatedly(_lll_reduce!, B, δ, η)
end

function _lll_reduce!(B::AbstractMatrix{T}, δ::Real, η::Real) where T<:Number
    n, m = size(B)

    Q, R = geometric_normal_form(B)
    #println("start: $(target(diag(R)))")
    ok = true

    inttype(::Type{T}) where T = typeof(Integer(one(T)))
    k = 2
    while k <= m
        l = max(k - 1, 1) # in 1:k - 1
        for i = k-1:-1:l
            while true
                rii = abs2(real(R[i, i])) * η^2
                max(abs2(real(R[i, k])), abs2(imag(R[i, k]))) <= rii && break
                ok &= decrease!(R, B, i, k)
                #println("($i,$k) decrease1 $(inorm(B * M, 1))")
                #display(M)
            end
        end
        if abs2(R[k, k]) + abs2(R[k-1, k]) < δ * abs2(R[k-1, k-1]) # note: typo in paper
            swap!(R, B, Q, k)
            dev = norm((Q'*B-R)[1:k, 1:k]) / norm(R[1:k, 1:k])
            #println("$k: $(target(R)) $dev norm(R) = $(norm(R[1:k,1:k])) $ok")
            if dev > 1e-8 || !ok
                ok = true
                Q, R = geometric_normal_form(B)
                #println("$k: $(target(R)) $dev (reorth)")
            end
            #println("($(k-1),$k)      swap $(inorm(B * M, 1))")
            #display(M)
            k = max(2, k - 1)
        else
            for i = l-1:-1:1
                while true
                    rii = abs2(real(R[i, i])) * η^2
                    max(abs2(real(R[i, k])), abs2(imag(R[i, k]))) <= rii && break
                    ok &= decrease!(R, B, i, k)
                    #println("($i,$k) decrease2 $(inorm(B * M, 1))")
                    #display(M)
                end
            end
            k += 1
        end
    end
    B, R, Q, ok
end

function call_repeatedly(f!::Function, B::AbstractMatrix, args...)
    bn = Inf
    res = f!(B, args...)
    bold, bn = bn, norm(B)
    i = 0
    while bn < bold
        i += 1
        res = f!(B, args...)
        bold, bn = bn, norm(B)
        #println("$i $bn $(target(res[2]))")
    end
    res
end

inorm(B, a...) = sum(abs2.(B))

# qr without pivoting - then normalize diagonal of R
function geometric_normal_form(B)
    Q, R = qr(B)
    D = Diagonal(sign.(diag(R)))

    R = D \ R # enforce R[i,i] > 0
    Q = Matrix(Q) * D
    Q, R
end
target(R::AbstractMatrix) = target(diag(R))
function target(R::AbstractVector)
    d = size(R, 1)
    sum(log2(abs2(R[i])) * (d - i + 1) for i = 1:d)
end

function decrease!(R, M, i, j)
    rm = axes(M, 1)
    γ = round(R[i, j] / R[i, i])
    R[1:i, j] .-= R[1:i, i] * γ
    M[rm, j] .-= M[rm, i] * eltype(M)(γ)
    eps(abs(γ)) < 1.0
end

function swap!(R, M, Q, i)
    m = size(R, 2)
    swapcols!(R, i - 1, i, 1:i)
    swapcols!(M, i - 1, i, axes(M, 1))
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
    for k in axes(Q, 1)
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
    rational_relationship(a; e=1e-5, c=1e9)

Given a vector of numbers `a`, find small integers `m` such that `m' * a` is small.
The constant `c` is used to set up the initial matrix to be `lll_reduce`d.

"""
function rational_relationship(
    a::Vector{<:Number};
    e::AbstractFloat = 1e-5,
    c::Number = 1e9,
)
    B = [c * a'; I]
    M, R, Q = lll_reduce(B)
    m = M[2:end, 1]
    d = abs(m'a)
    d > e && throw(ArgumentError("no convergence"))
    m
end

function minimal_polynomial(a::Number, n::Integer; e=1e-5, c=1e9)
    m = rational_relationship([a^i for i = 0:n]; e, c)
    p = ZZ{Int}[:x](m)
    p / lcunit(p)
end

export lll_reduce, rational_relationship
