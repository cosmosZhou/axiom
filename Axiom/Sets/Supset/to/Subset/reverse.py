from util import *


@apply
def apply(given):
    A, B = given.of(Supset)
    return Subset(B, A)


@prove
def prove(Eq):
    from Axiom import Sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Supset(A, B))

    Eq << Sets.Subset.of.All_In.apply(Eq[1])

    Eq << Sets.Supset.to.All_In.apply(Eq[0])


if __name__ == '__main__':
    run()
# created on 2021-06-25
