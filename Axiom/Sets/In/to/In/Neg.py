from util import *


@apply
def apply(given):
    e, interval = given.of(Element)

    return Element(-e, -interval)


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq <<= Eq[-1].reversed, Eq[-2].reversed

    Eq << Sets.In_Interval.of.And.apply(Eq[1])


if __name__ == '__main__':
    run()

# created on 2018-05-14
