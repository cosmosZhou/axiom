from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive

    e, interval = given.of(Element)

    a, b = interval.of(Interval)

    return Element(e / d, interval.copy(start=a / d, stop=b / d))


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b = Symbol(real=True)
    # t = Symbol(real=True)
    d = 2
    Eq << apply(Element(x, Interval(a, b)), d)

    Eq << Sets.In_Interval.to.And.apply(Eq[0])

    Eq <<= Eq[-2] / d, Eq[-1] / d

    Eq << Sets.In_Interval.of.And.apply(Eq[1])




if __name__ == '__main__':
    run()

# created on 2018-07-08
