from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Range)

    if interval.right_open:
        return Greater(b, x)
    else:
        if interval.left_open:
            return Greater(x, a)


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Sets.In_Range.to.And.apply(Eq[0])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-05-03
del domain
from . import domain