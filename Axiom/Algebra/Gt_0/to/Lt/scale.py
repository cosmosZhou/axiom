from util import *


@apply
def apply(given, t):
    x = given.of(Expr > 0)
    assert t < 1
    return Less(t * x, x)


@prove
def prove(Eq):
    from Axiom import Algebra

    a = Symbol(real=True, given=True)
    t = Symbol(domain=Interval.open(-oo, 1))
    Eq << apply(a > 0, t)

    Eq << Less(t - 1, 0, plausible=True)

    Eq << Algebra.Gt_0.Lt_0.to.Lt_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Add)

    Eq << Algebra.Lt_0.to.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-08-14