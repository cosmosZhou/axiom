from util import *


@apply
def apply(a_is_real, b_is_real):
    a, aR = a_is_real.of(Element)
    b, bR = b_is_real.of(Element)
    from axiom.sets.is_real.is_real.imply.is_real import interval_is_real
    assert interval_is_real(aR)
    assert interval_is_real(bR)
    return Element(a + b, Reals)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Reals), Element(y, Reals))

    Eq << sets.el.imply.any.eq.apply(Eq[0], var='a')

    Eq << sets.el.imply.any.eq.apply(Eq[1], var='b')

    Eq << algebra.any.any.imply.any.et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.add)

    a, b = Eq[-1].variables
    c = Symbol(real=True)
    Eq << algebra.any.imply.any.subs.apply(Eq[-1], a + b, c)




if __name__ == '__main__':
    run()
# created on 2022-04-03
