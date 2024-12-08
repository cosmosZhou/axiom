from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(Card(S | {e}), Card(S) + 1)


@prove
def prove(Eq):
    from Axiom import Sets

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << Sets.NotIn.to.Eq_EmptySet.Intersect.apply(Eq[0])

    Eq << Sets.Intersect_Eq_EmptySet.to.Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-17
