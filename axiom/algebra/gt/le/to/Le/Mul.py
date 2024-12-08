from util import *


@apply
def apply(gt, le):
    a, b = gt.of(Greater)
    x, y = le.of(LessEqual)
    z = a - b
    return LessEqual(z * x,  z * y)


@prove
def prove(Eq):
    from Axiom import Algebra
    a, b, x, y = Symbol(real=True)
    Eq << apply(a > b, x <= y)

    Eq << Algebra.Gt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-01
