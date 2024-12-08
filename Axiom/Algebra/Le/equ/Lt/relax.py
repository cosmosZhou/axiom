from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs.is_integer
    return Less(lhs, rhs + 1)


@prove
def prove(Eq):
    from Axiom import Algebra

    x, y = Symbol(integer=True)
    Eq << apply(x <= y)

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Le.to.Lt.relax)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.of.Lt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
