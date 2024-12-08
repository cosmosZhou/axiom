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

    Eq << Sets.Subset.to.Supset.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2021-07-02
