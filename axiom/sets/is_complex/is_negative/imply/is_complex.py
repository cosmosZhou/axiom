from util import *


@apply
def apply(is_complex, is_negative):
    a, R = is_negative.of(Element)
    assert R in Interval(-oo, 0, right_open=True)
    b, R = is_complex.of(Element)
    assert R in S.Complexes
    return Element(b / a, S.Complexes)


@prove
def prove(Eq):
    from axiom import sets
    
    x, y = Symbol(super_complex=True)
    Eq << apply(Element(y, S.Complexes), Element(x, Interval(-oo, 0, right_open=True)))
    
    Eq << sets.is_negative.is_complex.imply.is_complex.apply(Eq[1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-05-03
