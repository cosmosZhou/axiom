from util import *


@apply
def apply(gt_zero, ge):
    a, b = ge.of(GreaterEqual)
    x = gt_zero.of(Expr > 0)
    return gt_zero, GreaterEqual((a * x).expand(), (b * x).expand()).simplify()


@prove
def prove(Eq):
    from axiom import algebra

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, GreaterEqual(x + y, z))

    Eq << algebra.gt_zero.ge.imply.ge.div.apply(Eq[0], Eq[2])

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.add)

    


if __name__ == '__main__':
    run()
# created on 2023-10-03