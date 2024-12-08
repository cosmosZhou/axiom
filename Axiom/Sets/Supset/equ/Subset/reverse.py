from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return Subset(B, A)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Sets.Supset.to.Subset.reverse)
    Eq << Eq[-1].this.rhs.apply(Sets.Supset.of.Subset.reverse)


if __name__ == '__main__':
    run()
# created on 2021-07-09
