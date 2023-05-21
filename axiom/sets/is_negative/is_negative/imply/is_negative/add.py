from util import *


@apply
def apply(a_is_negative, b_is_negative):
    a, R = a_is_negative.of(Element)
    negative_R = Interval(-oo, 0, right_open=True)
    assert R in negative_R
    b, R = b_is_negative.of(Element)
    assert R in negative_R
    return Element(a + b, negative_R)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(-oo, 0, right_open=True)), Element(y, Interval(-oo, 0, right_open=True)))

    Eq << sets.el_interval.imply.lt.apply(Eq[0])

    Eq << sets.el_interval.imply.lt.apply(Eq[1])

    Eq << algebra.lt.lt.imply.lt.add.apply(Eq[-1], Eq[-2])
    Eq << sets.is_real.is_real.imply.is_real.add.apply(Eq[0], Eq[1])
    Eq << sets.lt_zero.is_complex.imply.is_negative.apply(Eq[-2], Eq[-1])
    


if __name__ == '__main__':
    run()
# created on 2023-05-03
