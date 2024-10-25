from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return Subset(B, A)


@prove
def prove(Eq):
    from axiom import algebra, sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(sets.supset.then.subset.reverse)
    Eq << Eq[-1].this.rhs.apply(sets.supset.of.subset.reverse)


if __name__ == '__main__':
    run()
# created on 2021-07-09
