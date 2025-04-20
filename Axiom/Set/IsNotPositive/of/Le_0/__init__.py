from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    assert x.is_finite
    return Element(x, Interval(-oo, 0))


@prove
def prove(Eq):
    from Axiom import Set, Algebra, Logic

    x = Symbol(complex=True)
    Eq << apply(x <= 0)

    Eq << Set.IsReal.of.Le.apply(Eq[0], simplify=None)

    Eq << Set.Or.of.Mem_Icc.apply(Eq[-1], 0, left_open=True)

    Eq <<= Eq[0] & Eq[-1]

    Eq << Logic.OrAndS.of.And_Or.apply(Eq[-1])

    Eq << Algebra.And.of.And.apply(Eq[-1], simplify=None)


if __name__ == '__main__':
    run()
# created on 2021-02-15

from . import IsComplex
