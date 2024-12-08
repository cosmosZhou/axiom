from util import *


@apply
def apply(is_positive_x, is_positive_y):
    x = is_positive_x.of(Expr > 0)
    y = is_positive_y.of(Expr > 0)
    return Greater(x / y, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x > 0, y > 0)

    Eq << Algebra.Gt_0.Gt.to.Gt.Div.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-05-02
