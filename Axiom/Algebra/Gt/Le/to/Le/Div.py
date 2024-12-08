from util import *


@apply
def apply(gt, le):
    if le.is_Greater:
        gt, le = le, gt
    x, y = gt.of(Greater)
    z = x - y
    lhs, rhs = le.of(LessEqual)
    return LessEqual(lhs / z, rhs / z)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y, a, b = Symbol(real=True)
    Eq << apply(x > y, a * (y - x) <= b)

    Eq << Algebra.Gt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Le.to.Le.Div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-08-01
