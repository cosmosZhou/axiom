from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain.left_open
    a, b = domain.of(Interval)
    assert b == a + 1
    return Equal(Ceiling(x), b)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Element(x, Interval(a, a + 1, left_open=True)))

    Eq << Sets.In.to.In.Sub.apply(Eq[0], a + 1)

    Eq << Sets.In.to.Eq_.Ceiling.Zero.apply(Eq[-1])
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-23
