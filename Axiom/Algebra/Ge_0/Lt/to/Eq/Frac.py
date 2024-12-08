from util import *


@apply
def apply(is_nonnegative, lt):
    x = is_nonnegative.of(Expr >= 0)
    S[x], M = lt.of(Less)

    return Equal(x, frac(x))


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(x >= 0, x < 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Frac.eq.Add).reversed

    Eq << Algebra.Ge_0.Lt.to.Eq_.Floor.Zero.apply(Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-03-07
