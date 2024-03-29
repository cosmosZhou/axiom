from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    RR = Interval.open(-oo, 0)
    assert R in RR
    return Element(1 / x, RR)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << sets.el.imply.any.eq.apply(Eq[0])

    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Less).apply(algebra.lt_zero.imply.lt_zero.div)

    Eq << Eq[-1].this.find(Less).apply(sets.lt_zero.imply.is_negative, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2020-04-13
# updated on 2022-04-03
