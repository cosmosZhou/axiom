from util import *


@apply
def apply(is_real, is_negative):
    a, R = is_negative.of(Element)
    assert R in Interval(-oo, 0, right_open=True)
    b, R = is_real.of(Element)
    assert R in Reals
    return Element(b / a, Reals)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(super_real=True)
    Eq << apply(Element(y, Interval(-oo, oo)), Element(x, Interval(-oo, 0, right_open=True)))

    Eq << sets.is_negative.is_real.imply.is_real.apply(Eq[1], Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2023-05-03
