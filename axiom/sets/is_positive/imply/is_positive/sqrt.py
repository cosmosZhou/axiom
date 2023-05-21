from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(0, oo, left_open=True)
    return Element(sqrt(x), R)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.is_positive.imply.is_real.apply(Eq[0])

    Eq << sets.el.imply.eq.definition.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << sets.is_positive.imply.gt_zero.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1], simplify=None)

    Eq << sets.gt_zero.imply.is_positive.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].subs(Eq[3])

    


if __name__ == '__main__':
    run()
# created on 2023-05-03
