from util import *


@apply
def apply(given, t):
    x = given.of(Expr >= 0)
    assert t <= 1
    return LessEqual(t * x, x)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(real=True, given=True)
    t = Symbol(domain=Interval(-oo, 1))
    Eq << apply(a >= 0, t)

    Eq << LessEqual(t - 1, 0, plausible=True)

    Eq << Algebra.Le_0.Ge_0.to.Le_0.apply(Eq[-1], Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add)

    Eq << Algebra.Le_0.to.Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-06-16
