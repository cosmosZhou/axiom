from util import *


@apply
def apply(given):
    B, A = given.of(Equal[Card[Complement], 0])
    return Subset(B, A)


@prove
def prove(Eq):
    from axiom import sets
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(0, Card(B - A)))

    Eq << sets.is_zero.then.is_empty.apply(Eq[0])

    Eq << sets.is_empty.then.subset.complement.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-06
