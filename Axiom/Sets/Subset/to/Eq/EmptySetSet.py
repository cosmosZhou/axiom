from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    assert not B

    return Equal(A, B)


@prove
def prove(Eq):
    from Axiom import Sets

    A = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, A.emptySet))

    Eq << Sets.Subset.to.Eq.Intersect.apply(Eq[0])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-09-14