from util import *


@apply
def apply(given, M=None):
    ((f, (z, xi)), S[f._subs(z, xi)]), (S[xi], domain) = given.of(All[Equal[Limit]])
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert b >= a
    if M is None:
        M = given.generate_var(real=True, var='M')
    return Any[M](All[z:domain](f <= M))


@prove
def prove(Eq):
    from axiom import calculus, algebra

    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))

    Eq << calculus.is_continuous.imply.any.all.le.extreme_value_theorem.apply(Eq[0])

    Eq << algebra.any.imply.any.limits.relax.apply(Eq[-1], domain=Reals)

    m = Eq[1].variable
    Eq << algebra.any.given.any.subs.apply(Eq[1], m, f(Eq[-1].variable))


if __name__ == '__main__':
    run()
# created on 2020-06-14
