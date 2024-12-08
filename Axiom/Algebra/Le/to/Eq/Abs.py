from util import *


@apply
def apply(given):
    x, y = given.of(LessEqual)
    return Equal(abs(x - y), -x + y)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x <= y)

    Eq << Algebra.Le.to.Le_0.apply(Eq[0])

    Eq << Algebra.Le_0.to.Eq.Abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-30
