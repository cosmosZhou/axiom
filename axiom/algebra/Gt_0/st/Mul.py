from util import *


@apply
def apply(given):
    args = given.of(Mul > 0)
    args = [arg for arg in args if not arg > 0]
    return Mul(*args) > 0


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x * a > 0)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.to.Gt_0.Mul, 1 / a)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.to.Gt_0.Mul, a)


if __name__ == '__main__':
    run()
# created on 2023-11-05
