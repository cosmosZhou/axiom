from util import *


@apply
def apply(eq):
    x, a = eq.of(Equal[Ceiling])
    return Element(x, Interval(a - 1, a, left_open=True, right_open=False))


@prove
def prove(Eq):
    from axiom import sets

    x = Symbol(real=True)
    a = Symbol(integer=True)
    Eq << apply(Equal(Ceiling(x), a + 1))

    Eq << sets.el.imply.eq.ceiling.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-05-29
