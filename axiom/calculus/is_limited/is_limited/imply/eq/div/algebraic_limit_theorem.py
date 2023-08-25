from util import *


@apply
def apply(limited_f, limited_g):
    from axiom.calculus.is_limited.imply.any.all.limit_definition import of_limited
    fx, (x, x0, S[0]) = of_limited(limited_f, real=True)
    gx, S[(x, x0, 0)] = of_limited(limited_g, nonzero=True)

    return Equal(Limit[x:x0](fx / gx), limited_f.lhs / limited_g.lhs)


@prove
def prove(Eq):
    from axiom import calculus, sets, algebra

    x, x0 = Symbol(real=True)
    f, g = Function(real=True)
    Eq << apply(Element(Limit[x:x0](f(x)), Reals), Element(Limit[x:x0](g(x)), Reals - {0}))

    Eq.inverse = calculus.is_limited.imply.eq.inverse.algebraic_limit_theorem.apply(Eq[1])

    Eq << sets.el.imply.is_real.inverse.apply(Eq[1])

    Eq << algebra.eq.cond.imply.cond.subs.apply(Eq.inverse, Eq[-1], reverse=True)

    Eq << calculus.is_limited.is_limited.imply.eq.mul.algebraic_limit_theorem.apply(Eq[0], Eq[-1])
    Eq << Eq[-1].subs(Eq.inverse)


if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Limit_of_a_function#Properties

# created on 2020-06-22
