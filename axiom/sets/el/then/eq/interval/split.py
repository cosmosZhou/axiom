from util import *


@apply
def apply(given, right_open=True):
    x, interval = given.of(Element)
    a, b = interval.of(Interval)
    return Equal(interval, Interval(a, x, left_open=interval.left_open, right_open=right_open) | Interval(x, b, left_open=not right_open, right_open=interval.right_open))


@prove
def prove(Eq):
    from axiom import sets, algebra

    x, a, b, t = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), right_open=False)

    Eq << sets.eq.of.et.infer.apply(Eq[1], t)

    Eq <<= Eq[-2].this.rhs.apply(sets.el_union.of.ou), Eq[-1].this.lhs.apply(sets.el_union.then.ou)

    Eq <<= Eq[-2].this.lhs.apply(sets.el_interval.then.et), Eq[-1].this.rhs.apply(sets.el_interval.of.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.of.et), Eq[-1].this.find(Element).apply(sets.el_interval.then.et)

    Eq <<= Eq[-2].this.find(Element).apply(sets.el_interval.of.et), Eq[-1].this.find(Element).apply(sets.el_interval.then.et)

    Eq << algebra.infer_ou.of.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer.of.infer.split.et.apply(Eq[-2], 1), algebra.infer.of.infer.split.et.apply(Eq[-1], 0)

    Eq << sets.el_interval.then.et.apply(Eq[0])

    Eq <<= algebra.cond.then.infer.apply(Eq[-2], cond=t > x), algebra.cond.then.infer.apply(Eq[-1], cond=t <= x)

    Eq <<= algebra.infer_et.then.infer.et.apply(Eq[-2]), algebra.infer_et.then.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.apply(algebra.gt.gt.then.gt.trans), Eq[-1].this.rhs.apply(algebra.le.le.then.le.trans)


if __name__ == '__main__':
    run()
# created on 2020-11-22
