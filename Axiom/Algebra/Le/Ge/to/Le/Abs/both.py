from util import *


@apply
def apply(x_less_than_y, x_greater_than_y_minus):
    x, y = x_less_than_y.of(LessEqual)
    S[x], S[-y] = x_greater_than_y_minus.of(GreaterEqual)
    return LessEqual(abs(x), abs(y))


@prove
def prove(Eq):
    from Axiom import Algebra
    y, x = Symbol(real=True)

    Eq << apply(x <= y, x >= -y)

    Eq << Algebra.Le.Ge.to.Ge.trans.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + y

    Eq << Eq[-1] / 2

    Eq << Algebra.Ge_0.to.Eq.Abs.apply(Eq[-1])

    Eq << Algebra.Le.Ge.to.Le.Abs.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + Eq[-2].reversed

    Eq << Eq[-1].this.apply(Algebra.Le.simp.terms.common)


if __name__ == '__main__':
    run()
# created on 2019-05-30
