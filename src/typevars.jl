
# functions to set and get associated user data in variable `instance` of `DataType`.
function settypevar!(t::Type{<:Ring}, val)
    if !isdefined(t, :instance)
        t.instance = Ref(val)
    end
    val
end

gettypevar(t::Type{<:Ring{T}}) where T = (t.instance[])::T

register!(t::Type{<:Ring{T}}, args...) where T = settypevar!(t, T(args...))

