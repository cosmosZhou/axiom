from util import *


@apply
def apply(given):
    ((f, (z, xi, S[0])), _f), (S[xi], domain) = given.of(All[Equal[Limit]])
    a, b = domain.of(Interval)
    assert domain.is_closed
    assert _f == f._subs(z, xi)
    assert b >= a
    return Any[xi:domain](All[z:domain](f >= _f))


@prove(proved=False)
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(real=True, domain=Interval.open(a, oo))
    f = Function(real=True)
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    Eq << apply(is_continuous(f, a, b))


if __name__ == '__main__':
    run()
# created on 2020-06-13
