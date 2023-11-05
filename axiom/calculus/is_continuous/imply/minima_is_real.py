from util import *


@apply
def apply(given):
    ((f, (z, xi)), S[f._subs(z, xi)]), (S[xi], domain) = given.of(All[Equal[Limit]])
    assert not xi.infinitesimality
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert b >= a
    return Element(Minima[z:domain](f), Reals)


@prove(proved=False)
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << calculus.is_continuous.imply.any.all.ge.extreme_value_theorem.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(algebra.all_ge.imply.ge_minima)

    Eq << algebra.imply.all.minima_le.apply(Eq[1].lhs)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[-2].variable)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq[-2])

    Eq << Element(Eq[-1].expr.rhs, Reals, plausible=True)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[-1], Eq[-2])
    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-06-16
