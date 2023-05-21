from util import *


@apply
def apply(a_is_positive, b_is_positive):
    a, R = a_is_positive.of(Element)
    positive_R = Interval(0, oo, left_open=True)
    assert R in positive_R
    b, R = b_is_positive.of(Element)
    assert R in positive_R
    return Element(a + b, positive_R)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)), Element(y, Interval(0, oo, left_open=True)))

    Eq << sets.el_interval.imply.gt.apply(Eq[0])

    Eq << sets.el_interval.imply.gt.apply(Eq[1])

    Eq << algebra.gt.gt.imply.gt.add.apply(Eq[-1], Eq[-2])

    Eq << sets.is_real.is_real.imply.is_real.add.apply(Eq[0], Eq[1])

    Eq << sets.gt_zero.is_complex.imply.is_positive.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-05-03
