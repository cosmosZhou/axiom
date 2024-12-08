from util import *


@apply
def apply(lt, le):
    a, b = lt.of(Less)
    x, y = le.of(LessEqual)
    z = b - a
    return LessEqual(z * x,  z * y)


@prove
def prove(Eq):
    from Axiom import Algebra

    a, b, x, y = Symbol(real=True)
    Eq << apply(a < b, x <= y)

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-01-05
