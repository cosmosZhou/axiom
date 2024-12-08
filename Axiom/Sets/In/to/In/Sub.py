from util import *


@apply
def apply(given, t):
    e, interval = given.of(Element)
    t = sympify(t)
    assert t.is_finite
    return Element(e + -t, interval + -t)


@prove
def prove(Eq):
    from Axiom import Sets

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b)), t)

    Eq << Sets.In.to.In.Add.apply(Eq[0], -t)


if __name__ == '__main__':
    run()

# created on 2018-04-08
