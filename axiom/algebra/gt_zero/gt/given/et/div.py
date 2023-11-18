from util import *


@apply
def apply(gt_zero, gt):
    a, b = gt.of(Greater)
    x = gt_zero.of(Expr > 0)
    return gt_zero, Greater((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, Greater(x + y, z))

    Eq << algebra.gt_zero.gt.imply.gt.mul.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    


if __name__ == '__main__':
    run()
# created on 2023-10-03
