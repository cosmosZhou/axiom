from util import *


@apply
def apply(a_is_positive, b_is_positive):
    a, R = a_is_positive.of(Element)
    RR = Interval.open(0, oo)
    assert R in RR
    b, R = b_is_positive.of(Element)
    assert R in RR
    return Element(a * b, RR)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)), Element(y, Interval.open(0, oo)))

    Eq << sets.el.imply.any_eq.apply(Eq[0], var='a')

    Eq << sets.el.imply.any_eq.apply(Eq[1], var='b')

    Eq << algebra.any.any.imply.any_et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.imply.eq.mul)

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.is_positive.imply.gt_zero, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.is_positive.imply.gt_zero)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    a, b = Eq[-1].variables
    c = Symbol(real=True)
    Eq << algebra.any.imply.any.subs.apply(Eq[-1], a * b, c)

    Eq << Eq[-1].this.find(Greater).apply(sets.gt_zero.imply.is_positive, simplify=None)

    Eq << algebra.any_et.imply.any.limits_absorb.apply(Eq[-1], 0)

    


if __name__ == '__main__':
    run()
# created on 2022-04-03

from . import add
# updated on 2023-05-13
