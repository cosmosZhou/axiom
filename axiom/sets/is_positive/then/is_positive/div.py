from util import *


@apply
def apply(given):
    x, domain = given.of(Element)
    R = Interval.open(0, oo)
    assert domain in R
    return Element(1 / x, R)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x = Symbol(hyper_real=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << sets.el.then.any.eq.apply(Eq[0])

    Eq << algebra.any.then.any.et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << Eq[-1].this.find(Greater).apply(algebra.gt_zero.then.gt_zero.div)

    Eq << Eq[-1].this.find(Greater).apply(sets.gt_zero.then.is_positive, simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.then.cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2020-04-14
# updated on 2023-05-03
