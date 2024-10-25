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

    Eq << sets.el.then.any.eq.apply(Eq[0], var='a')

    Eq << sets.el.then.any.eq.apply(Eq[1], var='b')

    Eq << algebra.any.any.then.any.et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.eq.then.eq.mul)

    Eq << algebra.any.then.any.et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.is_positive.then.gt_zero, simplify=None)

    Eq << Eq[-1].this.find(Element).apply(sets.is_positive.then.gt_zero)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.gt_zero.gt_zero.then.gt_zero)

    a, b = Eq[-1].variables
    c = Symbol(real=True)
    Eq << algebra.any.then.any.subs.apply(Eq[-1], a * b, c)

    Eq << Eq[-1].this.find(Greater).apply(sets.gt_zero.then.is_positive, simplify=None)

    Eq << algebra.any_et.then.any.limits_absorb.apply(Eq[-1], 0)




if __name__ == '__main__':
    run()
# created on 2022-04-03

from . import add
# updated on 2023-05-13
