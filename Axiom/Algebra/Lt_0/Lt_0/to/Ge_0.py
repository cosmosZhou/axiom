from util import *


@apply
def apply(is_negative_x, is_negative_y):
    x = is_negative_x.of(Expr < 0)
    y = is_negative_y.of(Expr < 0)
    return GreaterEqual(x * y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True)

    Eq << apply(x < 0, y < 0)

    Eq << Algebra.Lt_0.Lt_0.to.Gt_0.apply(Eq[0], Eq[1])

    Eq << Algebra.Gt_0.to.Ge_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-01-23
