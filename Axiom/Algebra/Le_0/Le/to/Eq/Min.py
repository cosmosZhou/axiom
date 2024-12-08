from util import *


@apply
def apply(is_nonpositive, le):
    x = is_nonpositive.of(Expr <= 0)
    y, S[x] = le.of(LessEqual)

    return Equal(Min(y ** 2, x ** 2), x ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= 0, y <= x)

    Eq << Eq[-1] - x ** 2

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Min)

    Eq << Algebra.Le_0.Le.to.Le.Square.apply(Eq[0], Eq[1])

    Eq << Algebra.Le.to.Ge_0.apply(Eq[-1])

    Eq << Algebra.Ge.to.Eq.Min.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-12-07
