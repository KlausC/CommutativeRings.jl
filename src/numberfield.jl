
# class constructors

# by default assume modulus is irreducible
function NF(a::A) where A<:AlgebraicNumber
    p = minimal_polynomial(a)
    Q = Quotient(typeof(p), p) # no check for irreducibility - compared to T / p
    new_class(NumberField{A,sintern(a),Q}, a)
end

# Constructors
category_trait(::Type{<:NumberField{A}}) where A = category_trait(basetype(A))
basetype(::Type{<:NumberField{A}}) where A = basetype(A)

function (::Type{<:NumberField{A,Id,Q}})(q::P) where {A,P,Id,Q}
    v = Q(q)
    NumberField{A,Id}(v, NOCHECK)
end

# promotion and conversion
Base.convert(::Type{T}, a::Union{Integer,Rational}) where T<:NumberField = T(a)
Base.convert(::Type{T}, a::Ring) where T<:NumberField = T(a)
Base.convert(::Type{T}, a::NumberField) where T<:NumberField = a

promote_rule(::Type{N}, ::Type{<:QQ}) where N<:NumberField = N
promote_rule(::Type{N}, ::Type{<:ZZ}) where N<:NumberField = N
promote_rule(::Type{N}, ::Type{<:Integer}) where N<:NumberField = N
promote_rule(::Type{N}, ::Type{<:Rational}) where N<:NumberField = N

# return the generator of this number field
@inline generator(t::Type{<:NumberField}) = gettypevar(t).generator

Base.show(io::IO, nf::NumberField) = show(io, nf.repr)

approx(nf::N) where N<:NumberField = value(nf.repr)(approx(generator(N)))

+(a::N, b::N) where {A,Id,N<:NumberField{A,Id}} =
    NumberField{A,Id}(a.repr + b.repr, NOCHECK)
-(a::N, b::N) where {A,Id,N<:NumberField{A,Id}} =
    NumberField{A,Id}(a.repr - b.repr, NOCHECK)
-(a::N) where {A,Id,N<:NumberField{A,Id}} = NumberField{A,Id}(-a.repr, NOCHECK)
*(a::N, b::N) where {A,Id,N<:NumberField{A,Id}} =
    NumberField{A,Id}(a.repr * b.repr, NOCHECK)
/(a::N, b::N) where {A,Id,N<:NumberField{A,Id}} =
    NumberField{A,Id}(a.repr / b.repr, NOCHECK)
inv(a::N) where {A,Id,N<:NumberField{A,Id}} = NumberField{A,Id}(inv(a.repr), NOCHECK)
isunit(a::N) where {A,Id,N<:NumberField{A,Id}} = isunit(a.repr)
iszero(a::N) where {A,Id,N<:NumberField{A,Id}} = iszero(a.repr)
isone(a::N) where {A,Id,N<:NumberField{A,Id}} = isone(a.repr)
zero(::Type{N}) where {A,Id,Q,N<:NumberField{A,Id,Q}} = NumberField{A,Id}(zero(Q), NOCHECK)
one(::Type{N}) where {A,Id,Q,N<:NumberField{A,Id,Q}} = NumberField{A,Id}(one(Q), NOCHECK)
monom(::Type{N}, k::Integer = 1) where {A,Id,Q,N<:NumberField{A,Id,Q}} =
    NumberField{A,Id}(monom(Q, k), NOCHECK)

minimal_polynomial(b::NumberField) = minimal_polynomial(AlgebraicNumber(b))

function field_polynomial(b::N) where N<:NumberField
    r = b.repr
    q = value(r)
    p = modulus(r) # == minimal_polynomial(generator(N))
    x = monom(typeof(p))
    m = det(x * I - companion(p, q))
    m
end

function field_polynomial(a::A, b::B) where {A<:AlgebraicNumber,B<:UnivariatePolynomial}
    field_polynomial(b(monom(NF(a))))
end
