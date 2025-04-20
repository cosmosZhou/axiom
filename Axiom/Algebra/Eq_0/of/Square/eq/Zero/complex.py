from util import *


@apply
def apply(given):
    x = given.of(Equal[Expr ** 2, 0])
    return Equal(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(complex=True, given=True)
    Eq << apply(Equal(x ** 2, 0))

    Eq << Eq[0].this.lhs.base.apply(Algebra.Expr.eq.MulAbs_ExpMulIArg)

    Eq << Algebra.OrEqS_0.of.Mul.eq.Zero.apply(Eq[-1])

    Eq << Algebra.Eq_0.of.Square.eq.Zero.apply(Eq[-1])
    Eq << Algebra.Eq_0.of.Norm.eq.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-11-11

