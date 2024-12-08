from util import *


@apply
def apply(given):
    B, A = given.of(Equal[Card[Complement], 0])
    return Subset(B, A)


@prove
def prove(Eq):
    from Axiom import Sets
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(0, Card(B - A)))

    Eq << Sets.Eq_0.to.Eq_EmptySet.apply(Eq[0])

    Eq << Sets.Eq_EmptySet.to.Subset.Complement.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-06
