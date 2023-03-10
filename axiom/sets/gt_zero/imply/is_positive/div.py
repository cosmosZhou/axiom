from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    a, b = domain.of(Interval)
    if domain.left_open:
        assert a >= 0
    else:
        assert a > 0

    return Element(1 / x, Interval(0, oo, left_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval(0, oo, left_open=True)))

    Eq << sets.el.imply.any_eq.apply(Eq[0])

    Eq << algebra.any.imply.any_et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.imply.gt_zero.div)

    Eq << Eq[-1].this.find(Greater).apply(sets.gt_zero.imply.is_positive, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)


if __name__ == '__main__':
    run()
# created on 2020-04-14
