from util import *


@apply
def apply(given):
    x, interval = given.of(Element)
    a, b = interval.of(Range)
    assert interval.right_open
    return a < b


@prove
def prove(Eq):
    from Axiom import Set, Algebra

    x, a, b = Symbol(integer=True)
    Eq << apply(Element(x, Range(a, b)))

    Eq << Set.And.of.Mem_Range.apply(Eq[0])

    Eq << Algebra.Lt.of.Ge.Lt.apply(*Eq[-2:])


if __name__ == '__main__':
    run()
# created on 2023-11-12
