from util import *


@apply
def apply(gt):
    x, a = gt.of(Abs > Expr)
    return Or(x < -a, x > a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) > a)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.GtAbs.to.Or)

    Eq << Eq[-1].this.lhs.apply(Algebra.GtAbs.of.Or)


if __name__ == '__main__':
    run()
# created on 2022-01-07
