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
    from Axiom import Calculus, Algebra

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from Axiom.Calculus.All_Eq.to.All.Any.Eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << Calculus.is_continuous.to.Any.All.Ge.extreme_value_theorem.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Algebra.All_Ge.to.GeMinima)

    Eq << Algebra.All_LeMinima.apply(Eq[1].lhs)

    Eq << Eq[-1].limits_subs(Eq[-1].variable, Eq[-2].variable)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq[-2])

    Eq << Element(Eq[-1].expr.rhs, Reals, plausible=True)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-2])
    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-06-16