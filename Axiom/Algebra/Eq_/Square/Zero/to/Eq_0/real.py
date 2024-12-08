from util import *


@apply
def apply(given):
    x = given.of(Equal[Expr ** 2, 0])
    assert x.is_extended_real
    return Equal(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Equal(x ** 2, 0))

    Eq << Algebra.Eq.to.Eq.Pow.apply(Eq[0], exp=S.One / 2)

    Eq << Algebra.Eq_.Abs.Zero.to.Eq_0.real.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-03-16
