
## Creation

new_ideal(::Type{R}, m::R) where R<:Ring = m
new_ideal(::Type{R}, mm::R...) where R<:Ring = new_ideal(r, mm)
function new_ideal(::Type{R}, mm::AbstractVector{R}) where R<:Ring
    id = Ideal{R}()
    for m in mm
        add(id, m)
    end
    id
end

# Arithmetic

# successively add to for Groebner basis
function add(id::Ideal{R}, m::R) where {T,R<:UnivariatePolynomial{T}}
    base = id.base
    push!(base, m)
    id
end
