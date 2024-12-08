from util import *


@apply
def apply(gt, ge):
    a, b = gt.of(Greater)
    x, y = ge.of(GreaterEqual)
    z = a - b
    return GreaterEqual(z * x,  z * y)


@prove
def prove(Eq):
    from Axiom import Algebra
    a, b, x, y = Symbol(real=True)
    Eq << apply(a > b, x >= y)

    Eq << Algebra.Gt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Ge.to.Ge.Mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-07-13
