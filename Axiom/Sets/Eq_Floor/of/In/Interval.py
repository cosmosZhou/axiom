from util import *


@apply
def apply(eq):
    x, a = eq.of(Equal[Floor])
    return Element(x, Interval(a, a + 1, left_open=False, right_open=True))


@prove
def prove(Eq):
    from Axiom import Sets

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Equal(Floor(x), a))

    Eq << Sets.In.to.Eq.Floor.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-05-29
