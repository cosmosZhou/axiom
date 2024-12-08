from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], y = lt.of(Less)

    return Equal(Max(y ** 2, x ** 2), y ** 2)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x >= 0, x < y)

    Eq << Algebra.Lt.to.Le.relax.apply(Eq[1])

    Eq << Algebra.Ge_0.Le.to.Eq.Max.apply(Eq[0], Eq[-1])








if __name__ == '__main__':
    run()
# created on 2019-06-22
