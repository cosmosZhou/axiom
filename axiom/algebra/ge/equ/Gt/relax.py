from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert lhs.is_integer
    return Greater(lhs, rhs - 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(integer=True)
    Eq << apply(x >= y)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ge.to.Gt.relax)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge.of.Gt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
