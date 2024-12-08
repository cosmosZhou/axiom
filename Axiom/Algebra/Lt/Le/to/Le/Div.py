from util import *


@apply
def apply(lt, le):
    if le.is_Less:
        lt, le = le, lt
    x, y = lt.of(Less)
    x = y - x
    lhs, rhs = le.of(LessEqual)
    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x < y, a * (y - x) <= b)

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Le.to.Le.Div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-01-05
