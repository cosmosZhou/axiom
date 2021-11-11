from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    return Equal(Card(A), 0)


@prove
def prove(Eq):
    from axiom import sets

    A = Symbol(etype=dtype.integer, given=True)

    Eq << apply(Equal(A, A.etype.emptySet))

    Eq << sets.eq.imply.eq.card.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2021-05-14
# updated on 2021-05-14
