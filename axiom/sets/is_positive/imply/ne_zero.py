from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval(0, oo, left_open=True)
    return Unequal(x, 0)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.is_positive.imply.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-05-03