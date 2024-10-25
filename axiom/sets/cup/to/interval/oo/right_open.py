from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(0, oo, right_open=True))


@prove
def prove(Eq):
    from axiom import sets, algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(k, k + 1, right_open=True)))

    Eq << sets.eq.of.et.infer.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_cup.then.any_el), Eq[-1].this.rhs.apply(sets.el_cup.of.any_el)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(sets.el_interval.then.ge), Eq[-1].this.rhs.apply(algebra.any.of.cond.subs, k, Floor(x))

    Eq <<= Eq[-2].this.lhs.apply(algebra.any.then.any.et.limits.unleash, simplify=None), algebra.infer.of.et.infer.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(sets.el_range.then.ge), algebra.infer.of.cond.apply(Eq[-2]), Eq[-1].this.rhs.apply(sets.el_range.of.et)

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.then.ge)

    Eq <<= Eq[-3].this.lhs.expr.apply(algebra.ge.ge.then.ge.trans), sets.el_interval.of.et.apply(Eq[-2])

    Eq << Eq[-3].this.lhs.apply(sets.ge_zero.then.is_nonnegative, simplify=None)

    Eq << algebra.then.lt.floor.apply(x)

    Eq << algebra.then.ge_floor.apply(x)




if __name__ == '__main__':
    run()
# created on 2021-02-14
# updated on 2023-05-14
