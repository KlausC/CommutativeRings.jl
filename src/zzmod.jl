
# construction
basetype(::Type{<:ZZmod{m,T}}) where {m,T} = T
depth(::Type{<:ZZmod}) = 1
lcunit(a::ZZmod) = one(a)
issimpler(a::T, b::T) where T<:ZZmod = deg(a) < deg(b)

function ZZmod{m,T}(a::Integer) where {m,T}
    mo = modulus(ZZmod{m,T})
    mo > 0 && return ZZmod{m,T}(mod(T(a), T(mo)), NOCHECK)
    throw(DomainError(m, "modulus > 0 required."))
end
ZZmod{m}(a::Integer) where m = ZZmod{m,typeof(m)}(oftype(m, a))
ZZmod(a::T, m::S) where {T,S} = ZZmod{m}(S(a))
ZZmod{m,T}(a::ZZmod{m,T}) where {m,T} = a
ZZmod{m,T}(a::ZZmod{m,S}) where {m,T,S} = ZZmod{m,T}(a.val)
ZZmod{m,T}(a::ZZ) where {m,T} = ZZmod{m,T}(a.val)

# class constructors for `Int/31` notation
/(::Type{T}, m::Integer) where T<:Base.BitInteger = ZZmod{T(m),T}
/(::Type{T}, m::Integer) where T<:BigInt = new_class(ZZmod{gensym(),T}, T(m))

copy(p::ZZmod) = typeof(p)(p.val)

#promotion and conversion
function _promote_rule(ZT::Type{ZZmod{m,S}}, ZS::Type{ZZmod{n,T}}) where {n,m,T,S}
    if modulus(ZT) == modulus(ZS)
        R = promote_type(T, S)
        if m == n 
            ZZmod{promote(n,m),R}
        elseif n isa Symbol
            ZZmod{n,R}
        else
            ZZmod{m,R}
        end
     else
         throw(PromotionError())
    end
end

function convert(ZT::Type{ZZmod{n,T}}, a::ZS) where {n,m,T,S,ZS<:ZZmod{m,S}}
    if modulus(ZT) == modulus(ZS)
        R = promote_type(S,T)
        mn = m == n ? promote(m, n)[1] : n isa Symbol ? n : m
        ZZmod{mn,R}(a.val)
    else
        throw(DomainError((ZT,a), "cannot convert "))
    end
end

# get type variable
modulus(t::Type{<:ZZmod{m,T}}) where {m,T} = m isa Integer ? T(m) : gettypevar(t).modulus
modulus(::T) where T<:ZZmod = modulus(T)

# arithmetic

function +(a::T, b::T) where T<:ZZmod
    mb = modulus(T) - b.val
    s = a.val < mb ? a.val + b.val : a.val - mb
    T(s, NOCHECK)
end
function -(a::T, b::T) where T<:ZZmod
    mb = modulus(T) - b.val
    s = a.val < b.val ? a.val + mb : a.val - b.val
    T(s, NOCHECK)
end
-(a::T) where T<:ZZmod = iszero(a.val) ? a : T(modulus(T) - a.val, NOCHECK)
*(a::T, b::T) where T<:ZZmod = T(mult_ZZmod(a.val, b.val, modulus(T)), NOCHECK)
*(a::T, b::Integer) where T<:ZZmod = T(mult_ZZmod(a.val, b, modulus(T)), NOCHECK)
*(a::Integer, b::T) where T<:ZZmod = T(mult_ZZmod(a, b.val, modulus(T)), NOCHECK)

inv(a::T) where T<:ZZmod = T(invmod2(a.val, modulus(T)), NOCHECK)
(a::T, n::Integer) where T<:ZZmod = T(powermod(a.val, n, modulus(T)), NOCHECK)

isunit(x::T) where T<:ZZmod = gcd(modulus(T), x.val) == 1
iszero(x::ZZmod) = iszero(x.val)
isone(x::ZZmod) = isone(x.val)
zero(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(zero(S), NOCHECK)
zero(::Type{ZZmod{m}}) where {m} = ZZmod{m,typeof(m)}(zero(m), NOCHECK)
one(::Type{<:ZZmod{m,S}}) where {m,S} = ZZmod{m,S}(one(S))
one(::Type{ZZmod{m}}) where {m} = ZZmod{m}(one(m))
==(a::ZZmod{m1},b::ZZmod{m2}) where {m1,m2} = modulus(a) == modulus(b) && a.val == b.val
hash(a::ZZmod, h::UInt) = hash(a.val, hash(modulus(a), h))

# implementation of checked multiplication
function mult_ZZmod(a::T, b::T, m::T) where T<:Integer
    p, ov = Base.mul_with_overflow(a, b)
    ov || return mod(p, m)
    T(mod(widemul(a, b), m))
end
function mult_ZZmod(a::T1, b::T2, c::T) where {T1<:Integer,T2<:Integer,T<:Integer}
    a = T(mod(a,c))
    b = T(mod(b,c))
    mult_ZZmod(a, b, c)
end

# improved version of invmod
function invmod2(n::T, m::T) where T<:Integer
    m == T(0) && throw(DomainError(m, "`m` must not be 0."))
    p = _unsigned(abs(m))
    q = n >= 0 ? rem(_unsigned(n), p) : p - rem(_unsigned(-n), p)
    !iszero(q) && p != q || throw(DomainError((n, m), "Greatest common divisor is $m"))
    r = invmod_unsigned(q, p)
    m < 0 ? T(r) + m : T(r)
    # The postcondition is: mod(widemul(r, n), m) == mod(T(1), m) && div(r, m) == 0
end
# assumptions is, that  0 <= n < m
function invmod_unsigned(n::T, m::T) where T<:Union{Unsigned,BigInt}
    n = n < m ? n : rem(n, m)
    g, r, y = gcdx(n, m)
    g != 1 && throw(DomainError((n, m), "Greatest common divisor is $g."))
    # For unsigned T, x might be close to typemax; add m to force a wrap-around.
    if _underflow(r)
        r += m
    end
    r
    # The postcondition is: mod(widemul(r, n), m) == mod(T(1), m) && div(r, m) == 0
end

_underflow(r::Signed) = r < 0
_underflow(r::T) where T<:Unsigned = Base.hastypemax(T) && typemax(T)>>1 < r

_unsigned(::Type{BigInt}) = BigInt
_unsigned(T::Type) = unsigned(T)
_unsigned(x::BigInt) = x
_unsigned(x::Integer) = unsigned(x)

function Base.show(io::IO, a::ZZmod)
    v = a.val
    m = modulus(a)
    if v > m÷2
        print(io, '-', signed(m-v), '°')
    else
        print(io, signed(v), '°')
    end
end

