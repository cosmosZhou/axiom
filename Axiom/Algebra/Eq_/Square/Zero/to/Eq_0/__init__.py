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

    Eq << Eq[0].this.lhs.base.apply(Algebra.Expr.eq.Mul.ExpI)

    Eq << Algebra.Mul.eq.Zero.to.OrEqS_0.apply(Eq[-1])

    Eq << Algebra.Eq_.Square.Zero.to.Eq_0.real.apply(Eq[-1])
    Eq << Algebra.Eq_.Abs.Zero.to.Eq_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-11-11
from . import real
