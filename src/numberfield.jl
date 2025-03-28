
# class constructors

# by default assume modulus is irreducible
"""
    NF(A::AlgebraicNumber)

Construct the `NumberField` class for `A`.
Elements of that field can be constructed by calling `NF(A)(p)` where `p` is a polynomial
or with `monomial(NF(A))`.
"""
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

function Base.show(io::IO, b::N) where N<:NumberField
    print(io, "NF ", value(b.repr), " over ", base(N))
end
function Base.show(io::IO, ::Type{N}) where N<:NumberField
    print(io, "NumberField over ", isconcretetype(N) ? base(N) : "?")
end

# promotion and conversion
Base.convert(::Type{T}, a::Union{Integer,Rational}) where T<:NumberField = T(a)
Base.convert(::Type{T}, a::Ring) where T<:NumberField = T(a)
Base.convert(::Type{T}, a::NumberField) where T<:NumberField = a

promote_rule(::Type{N}, ::Type{<:QQ}) where N<:NumberField = N
promote_rule(::Type{N}, ::Type{<:ZZ}) where N<:NumberField = N
promote_rule(::Type{N}, ::Type{<:Integer}) where N<:NumberField = N
promote_rule(::Type{N}, ::Type{<:Rational}) where N<:NumberField = N

# return the base algebraic number of this number field
@inline base(t::Type{<:NumberField}) = gettypevar(t).generator
@inline base(b::NumberField) = base(typeof(b))

approx(nf::N) where N<:NumberField = value(nf.repr)(approx(base(N)))

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

==(a::N, b::N) where N<:NumberField = value(a.repr) == value(b.repr)
function ==(a::NumberField, b::NumberField)
    va = value(a.repr)
    vb = value(b.repr)
    (0 >= deg(va) == deg(vb)) && va[0] == vb[0]
end
function hash(a::NumberField, x::UInt)
    if 0 >= deg(value(a.repr))
        hash(value(a.repr)[0])
    else
        hash(base(a), hash(a.repr, x))
    end
end

function zero(::Type{N}) where {A,Id,Q,N<:NumberField{A,Id,Q}}
    NumberField{A,Id}(zero(Q), NOCHECK)
end

function one(::Type{N}) where {A,Id,Q,N<:NumberField{A,Id,Q}}
    NumberField{A,Id}(one(Q), NOCHECK)
end

function monom(::Type{N}, k::Integer = 1) where {A,Id,Q,N<:NumberField{A,Id,Q}}
    NumberField{A,Id}(monom(Q, k), NOCHECK)
end

generator(::Type{N}) where N<:NumberField = monom(N)

minimal_polynomial(b::NumberField) = minimal_polynomial(AlgebraicNumber(b))

minimal_polynomial(::Type{N}) where N<:NumberField = minimal_polynomial(base(N))

"""
    field_matrix(b::NumberField)

Return the field matrix for number field element `b` in the standard basis.
"""
function field_matrix(b::N) where N <:NumberField
    p = minimal_polynomial(N)
    q = value(b.repr)
    companion(p, q)
end

"""
    field polynomial(b::NumberField)

The characteristic polynomial of any field matrix of an element `b` of a number field
over `a`.

The field matrix of `b` with the standard basis `a^0, a, ..., a^(n-1)` is the
`companion(p, q)`, where `p` is the minimal polynomial of `a` and `q` is the
polynomial representing `b (b = q(a))`.
"""
field_polynomial(b::NumberField) = characteristic_polynomial(field_matrix(b))
tr(b::NumberField) = tr(field_matrix(b))
norm(b::NumberField) = det(field_matrix(b))

function field_polynomial(a::A, b::B) where {A<:AlgebraicNumber,B<:UnivariatePolynomial}
    field_polynomial(b(monom(NF(a))))
end
