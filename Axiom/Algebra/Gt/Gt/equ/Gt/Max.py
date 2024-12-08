from util import *


@apply
def apply(gt_a, gt_b):
    x, a = gt_a.of(Greater)
    S[x], b = gt_b.of(Greater)
    return x > Max(a, b)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x > y, x > b)

    Eq << Algebra.Iff.of.And.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt.Gt.to.Gt.Max)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.Gt.of.Gt.Max)


if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-21
