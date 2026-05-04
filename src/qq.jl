
# class constructor
QQ(::Type{T}) where T<:Integer = QQ{T}
QQ(::Type{T}) where T<:ZI = QQ{basetype(T)}

Base.big(::Type{Q}) where Q<:QQ = QQ{big(basetype(Q))}

category_trait(::Type{<:QQ}) = FieldTrait
Base.IteratorSize(::Type{<:QQ}) = IsInfinite()

# construction
basetype(::Type{<:QQ{T}}) where T = ZZ{T}
basetype(::Type{<:QQ{T}}) where T<:ZI = T
#depth(::Type{<:QQ}) = 1
lcunit(a::QQ) = a < 0 ? -one(a) : one(a)
issimpler(a::T, b::T) where T<:QQ = QQ(abs(a.num), a.den) < QQ(abs(b.num), b.den)
copy(a::QQ) = typeof(a)(a.num, a.den)

value(a::QQ) = Rational(value(a.num), value(a.den))

QQ{T}(a::QQ) where T = QQ{T}(T(a.num), T(a.den), NOCHECK)
QQ{T}(a::ZI) where T = QQ{T}(T(value(a)), one(T), NOCHECK)
QQ{T}(a::Integer) where T = QQ{T}(T(a), one(T), NOCHECK)
QQ{T}(a::Rational{<:Integer}) where T = QQ{T}(T(a.num), T(a.den), NOCHECK)

QQ(a::QQ{T}) where T = a
QQ(a::T) where T<:ZI = QQ{basetype(T)}(a)
QQ(a::T) where T = QQ{T}(a)
QQ(a::Rational{T}) where T<:Integer = QQ{T}(a)

function QQ{T}(num::Union{Integer,ZZZ}, den::Union{Integer,ZZZ}) where T<:Union{Integer,ZZZ}
    iszero(num) &&
        iszero(den) &&
        throw(ArgumentError("invalid rational: zero($T)//zero($T)"))
    num == den && return one(QQ{T})
    R = promote_type(T, typeof(signed(num)), typeof(signed(den)))
    num1, den1 = Base.divgcd(num, den)
    num2, den2 = T(num1), T(den1)
    if signbit(den2)
        den2 = -den2
        signbit(den2) && throw(ArgumentError("invalid rational: denominator $den"))
        num2 = -num2
    end
    QQ{T}(num2, den2, NOCHECK)
end
function QQ(a::S, b::T) where {S<:Integer,T<:Integer}
    R = promote_type(typeof(signed(a)), typeof(signed(b)))
    QQ{R}(R(a), R(b))
end
QQ(num::T, den::T) where T = QQ{T}(num, den)
function QQ(num::ZI, den::ZI)
    num, den = promote(num, den)
    QQ(value(num), value(den))
end

value(a::Number) = a

Base.Rational(a::QQ{T}) where T = Rational(value(a.num), value(a.den))
//(a::T, b::T) where {T<:ZI} = QQ(Rational(value(a), value(b)))
Base.float(a::R) where {R<:Union{ZI,QQ}} = float(value(a))
(::Type{T})(a::R) where {R<:Union{ZI,QQ},T<:AbstractFloat} = T(value(a))

# promotion and conversion
promote_rule(::Type{QQ{T}}, ::Type{QQ{S}}) where {S,T} = QQ{promote_type(S, T)}
promote_rule(::Type{QQ{T}}, ::Type{S}) where {S<:ZI,T} = QQ{promote_type(basetype(S), T)}
promote_rule(::Type{QQ{T}}, ::Type{S}) where {S<:Integer,T} = QQ{promote_type(S, T)}
promote_rule(::Type{QQ{T}}, ::Type{Rational{S}}) where {S<:Integer,T} =
    QQ{promote_type(S, T)}

# induced homomorphism
function (h::Hom{F,R,S})(p::QQ{<:R}) where {F,R,S}
    QQ(h.f(a.num), h.f(a.den))
end

# operations for QQ
for op in (:+, :-, :*)
    @eval begin
        ($op)(a::QQ{T}, b::QQ{T}) where T = QQ(($op)(Rational(a), Rational(b)))
    end
end
==(a::T, b::T) where T<:QQ = Rational(a) == Rational(b)
/(a::T, b::T) where T<:QQ = iszero(b) ? throw(DivideError()) : QQ(Rational(a) / Rational(b))
-(a::T) where T<:QQ{<:Integer} = T(checked_neg(a.num), a.den)
-(a::T) where T = T(-a.num, a.den)
divrem(a::T, b::T) where T<:QQ = (a / b, zero(T))
div(a::T, b::T) where T<:QQ = a / b
rem(a::T, b::T) where T<:QQ = zero(T)
isless(a::T, b::T) where T<:QQ = isless(Rational(a), Rational(b))

isunit(a::QQ) = !iszero(a.num)
isone(a::QQ) = a.num == a.den
iszero(a::QQ) = iszero(a.num)
zero(::Type{QQ{T}}) where T = QQ{T}(zero(T), one(T), NOCHECK)
one(::Type{QQ{T}}) where T = QQ{T}(one(T), one(T), NOCHECK)
abs(a::QQ{T}) where T = QQ{T}(abs(a.num), abs(a.den), NOCHECK)
hash(a::QQ, h::UInt) = hash(Rational(a), h)

function show(io::IO, a::QQ)
    if isone(a.den)
        show(io, a.num)
    else
        print(io, a.num, '/', a.den)
    end
end
