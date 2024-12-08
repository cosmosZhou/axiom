from util import *


@apply
def apply(given, n):
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(x > 0, n)

    Eq.gt_zero, Eq.le_zero = Algebra.Cond.of.And.Imply.split.apply(Eq[1], cond=n > 0)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Gt_0.to.Gt_0.Pow)

    Eq << Algebra.Imply.of.And.Imply.split.apply(Eq.le_zero, cond=n < 0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq[-2])


    Eq << Eq[-1].this.lhs.apply(Algebra.Lt_0.Gt_0.to.Gt_0.Pow)


if __name__ == '__main__':
    run()
# created on 2018-08-22
# updated on 2023-04-15
