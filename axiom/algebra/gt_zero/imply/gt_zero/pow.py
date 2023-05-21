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

    Eq.gt_zero, Eq.le_zero = algebra.cond.given.et.infer.split.apply(Eq[1], cond=n > 0)

    Eq << algebra.infer.given.et.infer.et.apply(Eq.gt_zero, cond=Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.gt_zero.imply.gt_zero.pow)

    Eq << algebra.infer.given.et.infer.split.apply(Eq.le_zero, cond=n < 0)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << algebra.infer.given.et.infer.et.apply(Eq[-2], cond=Eq[0])

    
    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.gt_zero.imply.gt_zero.pow)


if __name__ == '__main__':
    run()
# created on 2018-08-22
# updated on 2023-04-15
