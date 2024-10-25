from util import *


@apply
def apply(given, n):
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(x > 0, n)

    Eq.gt_zero, Eq.le_zero = algebra.cond.of.et.infer.split.apply(Eq[1], cond=n > 0)

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.gt_zero.then.gt_zero.pow)

    Eq << algebra.infer.of.et.infer.split.apply(Eq.le_zero, cond=n < 0)

    Eq << algebra.infer.of.infer.subs.apply(Eq[-1])

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-2])


    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.gt_zero.then.gt_zero.pow)


if __name__ == '__main__':
    run()
# created on 2018-08-22
# updated on 2023-04-15
