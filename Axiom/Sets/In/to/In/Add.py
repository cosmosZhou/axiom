from util import *


@apply
def apply(given, t):
    e, interval = given.of(Element)
    assert t.is_finite
    return Element(e + t, interval + t)


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq <<= Eq[-1] + t, Eq[-2] + t

    Eq << Sets.Le.Ge.to.In.Interval.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-04-08
