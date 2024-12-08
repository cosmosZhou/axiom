from util import *


@apply
def apply(ge):
    x, a = ge.of(LessEqual)
    assert x > 0

    return GreaterEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, positive=True)
    a = Symbol(real=True)
    Eq << apply(x <= a)

    Eq << Algebra.Le.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Gt_0.Div.apply(Eq[-1])

    Eq << Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * x
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-31
