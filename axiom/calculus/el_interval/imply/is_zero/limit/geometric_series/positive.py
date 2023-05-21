from util import *


@apply
def apply(el, n):
    x, domain = el.of(Element)
    S[0], S[1] = domain.of(Interval)
    assert domain.left_open and domain.right_open
    return Equal(Limit[n:oo](x ** n), ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from axiom import calculus, algebra, sets

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, given=True)
    Eq << apply(Element(x, Interval(0, 1, left_open=True, right_open=True)), n)

    Eq << calculus.eq_limit.given.any_all.limit_definition.restricted.apply(Eq[1])

    Eq << Eq[-1].this.find(Less).apply(algebra.lt.given.lt.log)

    Eq.gt_zero = sets.el_interval.imply.gt.apply(Eq[0])

    Eq << algebra.gt_zero.imply.eq.abs.apply(Eq.gt_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.gt_zero.imply.eq.log.apply(Eq.gt_zero, Eq[-1].find(All).variable)

    Eq.any = Eq[-2].subs(Eq[-1])

    Eq.lt_zero = sets.el_interval.imply.lt_zero.log.apply(Eq[0])

    Eq << Element(Eq.any.find(Mul < ~Log), Interval(-oo, 0, right_open=True), plausible=True)

    Eq << sets.lt_zero.el.imply.el.div.apply(Eq.lt_zero, Eq[-1], simplify=None)

    Eq.ceiling_el = sets.el_interval.imply.el_range.ceiling.apply(Eq[-1])

    Eq << algebra.any.given.cond.subs.apply(Eq.any, Eq.any.variable, Eq.ceiling_el.lhs)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << algebra.all.given.infer.apply(Eq[-1])

    Eq << algebra.imply.ceiling_ge.apply(Eq.ceiling_el.lhs.arg)

    Eq << algebra.ge.imply.gt.relax.apply(Eq[-1], plus=True)

    Eq << algebra.infer.given.et.infer.et.apply(Eq[-3], cond=Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.ge.gt.imply.gt.transit)

    Eq << algebra.infer.given.et.infer.et.apply(Eq[-1], cond=Eq.lt_zero)


    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.gt.imply.lt.mul)


if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-04-17
