from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    assert x <= 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from Axiom import Algebra

    x = Symbol(nonpositive=True)
    Eq << apply(x >= 0)

    Eq << LessEqual(x, 0, plausible=True)

    Eq << Algebra.Le_0.Ge_0.to.Eq_0.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()

# created on 2019-06-16

del Min
from . import Min
