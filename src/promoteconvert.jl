
# promotions

_xpromote_rule(::Type{T},::Type{S}) where {T<:Ring,S<:RingInt} = begin
    depth(T) < depth(S) && return Base.Bottom
    B = basetype(T)
    (S <: T || S <: B) ? T : promote_rule(B, S) == B ? T : Base.Bottom
end
_xpromote_rule(a::Type, b::Type) = promote_rule(a, b)

@generated function Base.promote_rule(a::Type{<:Ring}, b::Type{<:RingInt})
    bt = _xpromote_rule(a.parameters[1], b.parameters[1])
    :($bt)
end

function promote_rule(::Type{R}, ::Type{S}) where {R<:Ring,S<:Rational}
    promote_rule(R, promote_type(basetype(R), S))
end

# abstract float involved
promote_rule(::Type{A}, ::Type{<:QQ{B}}) where {A<:AbstractFloat,B} = promote_rule(A, B)
promote_rule(::Type{A}, ::Type{<:ZZ{B}}) where {A<:AbstractFloat,B} = promote_rule(A, B)

# convertions
convert(::Type{T}, a) where T<:Ring = T(a)
function convert(::Type{T}, a::S) where {T<:Ring,S<:Ring}
    if !(S <: basetype(T)) && depth(T) > depth(S)
        b = convert(basetype(T), a)
        convert(T, b)
    else
        T(a)
    end
end

function convert(::Type{A}, a::Union{ZZ,QQ}) where {A<:AbstractFloat}
    convert(A, value(a))
end

function (G::Type{<:Ring})(a::Any)
    B = basetype(G)
    # println("G = $G $(isconcretetype(G)) B = $B $(isconcretetype(B))")
    isconcretetype(B) ? G(convert(B, a)) : throw(MethodError(G, Ref(a)))
end