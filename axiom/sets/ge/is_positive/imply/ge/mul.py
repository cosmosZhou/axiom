from util import *


@apply
def apply(lt, is_positive):
    x, R = is_positive.of(Element)
    assert R in Interval.open(0, oo)
    lhs, rhs = lt.of(GreaterEqual)
    return GreaterEqual(lhs * x, rhs * x)


@prove
def prove(Eq):
    from axiom import sets, algebra

    a, b = Symbol(real=True)
    x = Symbol(hyper_real=True)
    Eq << apply(a >= b, Element(x, Interval.open(0, oo)))

    Eq << sets.el.imply.any.eq.apply(Eq[1])

    Eq << algebra.any.imply.any.et.limits.unleash.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Element).simplify()

    Eq << algebra.cond.any.imply.any.et.apply(Eq[0], Eq[-1], simplify=None)

    Eq << Eq[-1].this.expr.args[1:].apply(algebra.gt_zero.ge.imply.ge.mul)

    Eq << Eq[-1].this.expr.apply(algebra.eq.cond.imply.cond.subs, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2023-05-14
