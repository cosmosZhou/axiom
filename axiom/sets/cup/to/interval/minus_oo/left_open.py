from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, 0))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, left_open=True)))

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.then.any_el), Eq[-1].this.rhs.apply(sets.el_cup.of.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_interval.then.ge), Eq[-1].this.rhs.apply(algebra.any.of.cond.subs, k, -Ceiling(x))

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.then.any.et.limits.unleash, simplify=None), algebra.infer.of.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(sets.el_range.then.ge), Eq[-1].this.rhs.apply(sets.el_range.of.et), algebra.infer.of.cond.apply(Eq[-2])

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.ge.ge.then.ge.add), -Eq[-2].this.rhs, sets.el_interval.of.et.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(sets.le_zero.then.is_nonpositive, simplify=None)

    Eq << algebra.then.gt.ceiling.apply(x)

    Eq << Eq[-3].this.lhs.apply(sets.el_interval.then.le)

    Eq << Eq[-1].this.lhs.apply(algebra.le_zero.then.ceiling_le_zero)

    Eq << algebra.then.le_ceiling.apply(x)





if __name__ == '__main__':
    run()
# created on 2021-02-16
# updated on 2023-05-19
