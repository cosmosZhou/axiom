from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    return Supset(B, A)


@prove
def prove(Eq):
    from Axiom import Sets

    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B))

    Eq << Sets.Supset.to.Subset.reverse.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2021-06-25
