from util import *


@apply
def apply(given):
    e, finiteset = given.of(Element[FiniteSet])

    return Or(*(Equal(e, s) for s in finiteset))


@prove
def prove(Eq):
    from Axiom import Sets

    e, a, b, c = Symbol(integer=True, given=True)
    Eq << apply(Element(e, {a, b, c}))

    Eq << Sets.Or_Eq.to.In.FiniteSet.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-05-30
