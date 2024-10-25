from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Supset(B, A)


@prove
def prove(Eq):
    from axiom import algebra, sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << algebra.iff.of.et.infer.apply(Eq[0])
    Eq << Eq[-2].this.lhs.apply(sets.subset.then.supset.reverse)
    Eq << Eq[-1].this.rhs.apply(sets.subset.of.supset.reverse)


if __name__ == '__main__':
    run()
# created on 2021-06-30
