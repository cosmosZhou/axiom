from util import *


@apply(simplify=None)
def apply(given):
    x, y = given.of(Unequal)
    return NotElement(x, y.set)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << ~Eq[0]

    Eq << Sets.Eq.to.In.FiniteSet.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2023-05-20