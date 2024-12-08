from util import *


@apply
def apply(given):
    x = given.of(Abs <= 0)
    return Equal(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(real=True)
    Eq << apply(abs(x) <= 0)

    Eq << Algebra.Le_0.to.Eq_0.apply(Eq[0])
    Eq << Algebra.Eq_.Abs.Zero.to.Eq_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-08-01
