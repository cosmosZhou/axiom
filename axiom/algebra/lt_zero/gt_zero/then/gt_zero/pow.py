from util import *


@apply
def apply(gt_zero, given):
    n = gt_zero.of(Expr < 0)
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from axiom import algebra

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(n < 0, x > 0)

    Eq << algebra.gt_zero.then.gt_zero.div.apply(Eq[1])

    Eq << algebra.gt_zero.gt_zero.then.gt_zero.pow.apply(-Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-15
