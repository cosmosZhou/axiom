from util import *


@apply
def apply(imply, right_open=True):
    x, interval = imply.of(Element)
    a, b = interval.of(Range)
    if right_open:
        return x >= a, x < b
    else:
        return x >= a, x <= b - 1


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    x, a, b = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Range(a, b)), right_open=False)

    Eq << Algebra.Le.to.Lt.relax.apply(Eq[-1], upper=b)

    Eq << Sets.Lt.to.In.Range.apply(Eq[-1])

    Eq << Sets.Ge.to.In.Range.apply(Eq[1])

    Eq <<= Eq[-2] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2018-03-01
from . import split
