from util import *


@apply
def apply(a_is_complex, b_is_complex):
    a, C = a_is_complex.of(Element)
    assert C in S.Complexes
    b, C = b_is_complex.of(Element)
    assert C in S.Complexes
    return Element(a + b, S.Complexes)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes), Element(y, S.Complexes))

    Eq << sets.el.then.any.eq.apply(Eq[0], var='a')

    Eq << sets.el.then.any.eq.apply(Eq[1], var='b')

    Eq << algebra.any.any.then.any.et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.then.eq.add)

    a, b = Eq[-1].variables
    c = Symbol(complex=True)
    Eq << algebra.any.then.any.subs.apply(Eq[-1], a + b, c)




if __name__ == '__main__':
    run()
# created on 2023-05-03
