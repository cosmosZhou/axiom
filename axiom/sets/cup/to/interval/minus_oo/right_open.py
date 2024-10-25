from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval.open(-oo, 0))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, right_open=True)))

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.then.any_el), Eq[-1].this.rhs.apply(sets.el_cup.of.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_interval.then.lt), Eq[-1].this.rhs.apply(algebra.any.of.cond.subs, k, -Floor(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.then.any.et.limits.unleash, simplify=None), algebra.infer.of.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(sets.el_range.then.le), Eq[-1].this.rhs.apply(sets.el_range.of.et), algebra.infer.of.cond.apply(Eq[-2])

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.le.lt.then.lt.add), Eq[-2].this.rhs.apply(algebra.ge.transport, lhs=0), sets.el_interval.of.et.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(sets.lt_zero.then.is_negative, simplify=None)

    Eq << algebra.then.ge_floor.apply(x)

    Eq << algebra.then.lt.floor.apply(x)

    Eq << -Eq[-3].this.rhs

    Eq << Eq[-1].this.rhs.apply(algebra.le.of.lt.one)

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.then.lt)

    Eq << Eq[-1].this.lhs.apply(algebra.lt_zero.then.floor_lt_zero)





if __name__ == '__main__':
    run()
# created on 2021-02-17
# updated on 2023-05-14
