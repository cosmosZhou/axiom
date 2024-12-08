from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Supset(B, A)


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Algebra.Iff.of.And.Imply.apply(Eq[0])
    Eq << Eq[-2].this.lhs.apply(Sets.Subset.to.Supset.reverse)
    Eq << Eq[-1].this.rhs.apply(Sets.Subset.of.Supset.reverse)


if __name__ == '__main__':
    run()
# created on 2021-06-30
