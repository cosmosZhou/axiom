from util import *


@apply
def apply(is_positive_x, ge):
    x = is_positive_x.of(Expr > 0)
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a >= b)

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[0])

    Eq << Algebra.Gt_0.Ge.to.Ge.Mul.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-07-20