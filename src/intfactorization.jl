
function factor(p::P) where P<:UnivariatePolynomial{<:ZZ}
    c = content(p)
    q = primpart(p)
    r = yun(q)
    s = zassenhaus(r)
    isone(c) ? s : [P(c) => 1; s]
end

function yun(p)
    p
end

function zassenhaus(p)
    [p => 1]
end