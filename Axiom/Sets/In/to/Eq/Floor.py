from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain.right_open
    a, b = domain.of(Interval)
    assert b == a + 1
    return Equal(Floor(x), a)


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Element(x, Interval(a, a + 1, right_open=True)))

    Eq << Sets.In.to.In.Sub.apply(Eq[0], a)

    Eq << Sets.In.to.Eq_.Floor.Zero.apply(Eq[-1])

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-12-05
