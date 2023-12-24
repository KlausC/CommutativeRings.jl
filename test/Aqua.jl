using Aqua

Aqua.test_all(
    CommutativeRings;
    ambiguities = true,
    stale_deps = true,
    deps_compat = true,
    piracies = (treat_as_own = [Base.binomial],),
)
