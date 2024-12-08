from util import *


@apply
def apply(is_complex, is_positive):
    a, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    b, R = is_complex.of(Element)
    assert R in S.Complexes
    return Element(b / a, S.Complexes)


@prove
def prove(Eq):
    from Axiom import Sets

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(y, S.Complexes), Element(x, Interval.open(0, oo)))

    Eq << Sets.is_positive.is_complex.to.is_complex.apply(Eq[1], Eq[0])




if __name__ == '__main__':
    run()
# created on 2023-05-03
