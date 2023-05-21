from util import *


@apply
def apply(is_positive, is_real):
    a, R = is_positive.of(Element)
    assert R in Interval(0, oo, left_open=True)
    b, R = is_real.of(Element)
    assert R in Reals
    return Element(b / a, Reals)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(super_real=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)), Element(y, Interval(-oo, oo)))

    Eq << sets.is_positive.imply.is_positive.div.apply(Eq[0])

    Eq << sets.is_real.is_real.imply.is_real.apply(Eq[-1], Eq[1])

    


if __name__ == '__main__':
    run()
# created on 2023-05-03
