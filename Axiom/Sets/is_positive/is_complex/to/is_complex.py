from util import *


@apply
def apply(is_positive, is_complex):
    a, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    b, R = is_complex.of(Element)
    assert R in S.Complexes
    return Element(b / a, S.Complexes)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, S.Complexes))

    Eq << Sets.is_positive.to.is_positive.Div.apply(Eq[0])


    Eq << Sets.is_complex.is_complex.to.is_complex.apply(Eq[-1], Eq[1])



if __name__ == '__main__':
    run()
# created on 2023-05-03
