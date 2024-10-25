from util import *


@apply
def apply(lt, contains, contains_y):
    x, domain_x = contains.of(Element)
    y, domain_y = contains_y.of(Element)
    assert domain_x in Interval(0, 1, right_open=True)
    assert domain_y in Interval(0, 1, right_open=True)
    S[x], S[y] = lt.of(Less)
    return y * sqrt(1 - x ** 2) > x * sqrt(1 - y ** 2)


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, y = Symbol(real=True)
    Eq << apply(x < y, Element(x, Interval(0, 1, right_open=True)), Element(y, Interval(0, 1, right_open=True)))

    Eq << sets.el_interval.then.ge.apply(Eq[1])

    Eq << algebra.ge.lt.then.gt.trans.apply(Eq[-1], Eq[0])

    Eq.y_contains = sets.gt.el_interval.then.el.interval.intersect.apply(Eq[-1], Eq[2])

    Eq << algebra.cond.of.et.infer.split.apply(Eq[3], cond=Equal(x, 0))

    Eq <<= algebra.infer.of.infer.subs.apply(Eq[-2]), algebra.cond.then.infer.et.apply(Eq[1], cond=Eq[-1].lhs)

    Eq << algebra.infer.of.cond.apply(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(sets.ne.el.then.el.complement)

    Eq << algebra.cond.infer.then.infer.et.rhs.apply(Eq.y_contains & Eq[0], Eq[-1])
    Eq << Eq[-1].this.rhs.apply(sets.lt.el.el.then.gt.sqrt.open.positive)


if __name__ == '__main__':
    run()
# created on 2020-11-28
