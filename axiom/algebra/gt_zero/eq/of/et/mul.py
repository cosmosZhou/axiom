from util import *


@apply
def apply(gt, eq):
    a, b = eq.of(Equal)
    x = gt.of(Expr > 0)
    return x > 0, Equal((a * x).expand(), (b * x).expand())#.simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, Equal(1 / x + y, z))

    Eq << algebra.gt_zero.then.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.eq.then.eq.div.apply(Eq[-1], Eq[2])





if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2023-11-06
