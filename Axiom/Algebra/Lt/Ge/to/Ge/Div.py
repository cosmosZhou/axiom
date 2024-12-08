from util import *


@apply
def apply(lt, ge):
    if ge.is_Less:
        lt, ge = ge, lt
    x, y = lt.of(Less)
    x = y - x
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x < y, a * (y - x) >= b)

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Ge.to.Ge.Div.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-12-13
