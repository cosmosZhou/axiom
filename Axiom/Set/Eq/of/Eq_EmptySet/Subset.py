from util import *


@apply
def apply(is_empty, subset):
    _B, C = is_empty.of(Equal[Intersection, EmptySet])
    A, B = subset.of(Subset)

    if B != _B:
        assert B == C
        C = _B

    return Equal(C - A, C)


@prove
def prove(Eq):
    from Axiom import Set
    A, B, C = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(B & C, C.etype.emptySet, evaluate=False), Subset(A, B, evaluate=False))

    Eq << Set.Eq_EmptySet.of.Eq_EmptySet.Subset.apply(Eq[0], Eq[1])

    Eq << Set.EqUnion.of.Eq.apply(Eq[-1], Eq[-2].lhs)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2021-05-15
