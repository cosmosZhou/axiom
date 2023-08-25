from util import *


@apply
def apply(is_negative, is_complex):
    a, R = is_negative.of(Element)
    assert R in Interval.open(-oo, 0)
    b, R = is_complex.of(Element)
    assert R in S.Complexes
    return Element(b / a, S.Complexes)


@prove
def prove(Eq):
    from axiom import sets

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)), Element(y, S.Complexes))

    Eq << sets.el.imply.el.neg.apply(Eq[0])

    Eq << sets.is_positive.is_complex.imply.is_complex.apply(Eq[-1], Eq[1])

    Eq << sets.el.imply.el.neg.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-05-03
