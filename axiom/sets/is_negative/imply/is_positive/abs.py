from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(-oo, 0)
    return Element(abs(x), -R)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << sets.is_negative.imply.lt_zero.apply(Eq[0])

    Eq << algebra.lt_zero.imply.eq.abs.apply(Eq[-1])

    Eq << Eq[1].subs(Eq[-1])

    Eq << sets.el.imply.el.neg.apply(Eq[0], simplify=None)




if __name__ == '__main__':
    run()
# created on 2020-04-15
# updated on 2023-04-18
