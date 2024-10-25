from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.then.any.all.limit_definition import of_limited
    fx, (x, x0) = of_limited(limited_f, real=True)
    gx, S[(x, x0)] = of_limited(limited_g, real=True)

    return Equal(Limit[x:x0](fx + gx), limited_f.lhs + limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Reals), Element(Limit[x:x0](g(x)), Reals))

    ε = Symbol(real=True, positive=True)
    ε_0 = Symbol(real=True, positive=True)
    δ_0 = Symbol(real=True, positive=True)
    Eq << calculus.is_limited.then.any.all.limit_definition.symbol_subs.apply(Eq[0], ε_0, δ_0, var='A')

    Eq << Eq[-1].subs(ε_0, ε / 2)

    ε_1 = Symbol(real=True, positive=True)
    δ_1 = Symbol(real=True, positive=True)
    Eq << calculus.is_limited.then.any.all.limit_definition.symbol_subs.apply(Eq[1], ε_1, δ_1, var='B')

    Eq << Eq[-1].subs(ε_1, ε / 2)

    Eq << algebra.any_all.any_all.then.any.all.et.limits_intersect.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.expr.apply(algebra.lt.lt.then.lt.abs.add)

    Eq << Eq[-1].this.find(And, Less).apply(sets.lt.of.el.interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[0].apply(sets.lt.of.el.interval)

    Eq << Eq[-1].this.expr.limits[0][1].args[1].simplify()

    δ = Symbol(real=True, positive=True)
    Eq << algebra.any.then.any.subs.apply(Eq[-1], Min(δ_0, δ_1), δ)

    Eq << calculus.any_all.then.eq.limit_definition.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[0].definition

    Eq << Eq[-1].this.rhs.args[0].definition


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function# Properties

# created on 2020-05-04
