from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    return x < 0


@prove
def prove(Eq):
    from Axiom import Algebra
    x = Symbol(real=True)

    Eq << apply(x <= 0)

    Eq << Algebra.Lt_0.to.Le_0.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-12-04
