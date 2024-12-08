from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(0, oo)
    return Element(x, Reals)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Sets.In.to.Eq.definition.apply(Eq[0])

    Eq << Eq[1].subs(Eq[-1].reversed)


if __name__ == '__main__':
    run()
# created on 2023-05-03
