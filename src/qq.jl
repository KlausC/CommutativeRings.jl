
# class constructor
QQ(::Type{T}) where T<:Integer = QQ{T}
QQ(::Type{ZZ{T}}) where T = QQ{T}

# construction
basetype(::Type{<:QQ{T}}) where T = ZZ{T}
depth(::Type{<:QQ}) = 1
issimpler(a::T, b::T) where T<:QQ = QQ(abs(a.num),a.den) < QQ(abs(b.num),b.den)
copy(a::QQ) = typeof(a)(a.num,a.den)

QQ(a::QQ{T}) where T = a
QQ{T}(a::QQ) where T = QQ{T}(T(a.num), T(a.den), NOCHECK)
QQ{T}(a::ZZ) where T = QQ{T}(T(a.val), one(T), NOCHECK)
QQ{T}(a::Integer) where T = QQ{T}(T(a), one(T), NOCHECK)
QQ{T}(a::Rational) where T = QQ{T}(T(a.num), T(a.den), NOCHECK)

function QQ{T}(num::Integer, den::Integer) where T<:Integer
    iszero(num) && iszero(den) && throw(ArgumentError("invalid rational: zero($T)//zero($T)"))
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
    R = promote_type(typeof(signed(a)),typeof(signed(b)))
    QQ{R}(R(a), R(b))
end
QQ(num::T, den::T) where T = QQ{T}(num, den)
QQ(a::Rational{T}) where T = QQ{T}(a.num, a.den)
QQ{T}(a::Rational) where T = QQ{T}(a.num, a.den)
Rational(a::QQ{T}) where T = Rational(a.num, a.den)
QQ{T}(a::Integer) where T = QQ{T}(T(a), one(T), NOCHECK)
QQ{T}(a::ZZ) where T = QQ{T}(T(a.val), one(T), NOCHECK)
QQ(a::ZZ{T}) where T = QQ{T}(a.val, one(T), NOCHECK)
QQ(a::T) where T<:Integer = QQ{T}(a, one(T), NOCHECK)
//(a::ZZ{T}, b::ZZ{T}) where T = QQ(Rational(a.val, b.val))

# promotion and conversion
_promote_rule(::Type{QQ{T}}, ::Type{QQ{S}}) where {S,T} = QQ{promote_type(S,T)}
_promote_rule(::Type{QQ{T}}, ::Type{ZZ{S}}) where {S,T} = QQ{promote_type(S,T)}
promote_rule(::Type{QQ{T}}, ::Type{S}) where {S<:Integer,T} = QQ{promote_type(S,T)}
promote_rule(::Type{QQ{T}}, ::Type{Rational{S}}) where {S,T} = QQ{promote_type(S,T)}

# induced homomorphism
function (h::Hom{F,R,S})(p::QQ{<:R}) where {F,R,S}
    QQ(h.f(a.num), h.f(a.den))
end

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
isless(a::T, b::T) where T<:QQ = isless(Rational(a), Rational(b))

isunit(a::QQ) = !iszero(a.num)
isone(a::QQ) = a.num == a.den
iszero(a::QQ) = iszero(a.num)
zero(::Type{QQ{T}}) where T = QQ{T}(zero(T), one(T), NOCHECK)
one(::Type{QQ{T}}) where T = QQ{T}(one(T), one(T), NOCHECK)
hash(a::QQ, h::UInt) = hash(Rational(a), h)

function show(io::IO, a::QQ)
    if isone(a.den)
        show(io, a.num)
    else
        print(io, a.num, '/', a.den)
    end
end
