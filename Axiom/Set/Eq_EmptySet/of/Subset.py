from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Equal(A - B, A.etype.emptySet)


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Subset(A, B))

    Eq << ~Eq[-1]

    Eq << Set.Any_Mem.of.Ne_EmptySet.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.Mem.et.NotMem.of.Mem_SDiff, simplify=None)

    Eq << Set.Any.of.Any_And.single_variable.limits_absorb.apply(Eq[-1], index=0, simplify=None)

    Eq << Set.Any.of.Any.limits.swap.apply(Eq[-1])

    Eq << Eq[-1].this.expr.apply(Set.Mem.of.Mem.Subset, Eq[0])

    Eq << Algebra.Any.And.of.Any.limits.single_variable.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-05-04
