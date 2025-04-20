from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return Subset(B, A)


@prove
def prove(Eq):
    from Axiom import Set

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << Set.Subset.given.All_Mem.apply(Eq[1])

    Eq << Set.All_Mem.of.Supset.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-06-25
