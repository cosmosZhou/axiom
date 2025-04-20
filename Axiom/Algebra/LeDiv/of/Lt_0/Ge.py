from util import *


@apply
def apply(is_negative, ge):
    x = is_negative.of(Expr < 0)
    # assert x.is_finite
    lhs, rhs = ge.of(GreaterEqual)
    return LessEqual(lhs / x, rhs / x)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a >= b)

    Eq << Algebra.Lt_0.Div.of.Lt_0.apply(Eq[0])

    Eq << Algebra.LeMul.of.Lt_0.Ge.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-10-28
