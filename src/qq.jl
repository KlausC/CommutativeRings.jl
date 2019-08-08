
# construction
basetype(::Type{<:QQ{T}}) where T = T
sign(a::QQ) = sign(a.num)
copy(a::QQ) = typeof(a)(a.num,a.den)
QQ{T}(a::QQ{T}) where T = a
QQ{T}(a::QQ{S}) where {T,S} = QQ{T}(a.num, a.den)

QQ(a::Rational{T}) where T = QQ{T}(a.num, a.den)
QQ{T}(a::Rational) where T = QQ{T}(a.num, a.den)
Rational(a::QQ{T}) where T = Rational(a.num, a.den)
QQ{T}(a::Integer) where T = QQ{T}(T(a), one(T))
QQ{T}(a::ZZ) where T = QQ{T}(T(a.val), one(T))
QQ(a::ZZ{T}) where T = QQ{T}(a.val, one(T))
QQ(a::T) where T<:Integer = QQ{T}(a, one(T))
//(a::ZZ{T}, b::ZZ{T}) where T = QQ(Rational(a.val, b.val))

promote_rule(::Type{QQ{T}}, ::Type{QQ{S}}) where {S,T} = QQ{promote_type(S,T)}
promote_rule(::Type{QQ{T}}, ::Type{S}) where {S<:Integer,T} = QQ{promote_type(S,T)}
promote_rule(::Type{QQ{T}}, ::Type{Rational{S}}) where {S,T} = QQ{promote_type(S,T)}
promote_rule(::Type{QQ{T}}, ::Type{ZZ{S}}) where {S,T} = QQ{promote_type(S,T)}

# operations for QQ
for op in (:+, :- , :*)
    @eval begin
        ($op)(a::QQ{T}, b::QQ{T}) where T = QQ(($op)(Rational(a), Rational(b)))
    end
end
==(a::T, b::T) where T<:QQ = Rational(a) == Rational(b)
/(a::T, b::T) where T<:QQ = iszero(b) ? throw(DivideError()) : QQ(Rational(a) / Rational(b))
-(a::QQ{T}) where T = QQ{T}(checked_neg(a.num),a.den)
divrem(a::T, b::T) where T<:QQ = (a / b, zero(T))
div(a::T, b::T) where T<:QQ = a / b
rem(a::T, b::T) where T<:QQ = zero(T)

isunit(a::QQ) = !iszero(a.num)
isone(a::QQ) = a.num == a.den
iszero(a::QQ) = iszero(a.num)
zero(::Type{QQ{T}}) where T = QQ(zero(T), one(T))
one(::Type{QQ{T}}) where T = QQ(one(T), one(T))
hash(a::QQ, h::UInt) = hash(Rational(a), h)

Base.show(io::IO, a::QQ) = show(io, Rational(a))
    
