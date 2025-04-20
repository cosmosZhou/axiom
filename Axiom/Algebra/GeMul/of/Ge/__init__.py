from util import *


@apply
def apply(given, factor):
    lhs, rhs = given.of(GreaterEqual)

    assert factor >= 0

    return GreaterEqual(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from Axiom import Algebra
    x, y = Symbol(real=True, given=True)
    k = Symbol(real=True, given=True, nonnegative=True)

    Eq << apply(GreaterEqual(x, y), k)

    Eq << GreaterEqual(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Ge.of.Ge_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-05-29

del Ge
from . import Ge
