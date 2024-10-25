from util import *


@apply
def apply(lt, x=None, left_open=True, right_open=True):
    m, M = lt.of(Less)
    return Equal(Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x), m)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, a, b = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x)

    Eq.eq_max = algebra.lt.then.eq.max.apply(Eq[0])

    Eq << algebra.eq.of.et.squeeze.apply(Eq[-1])

    y = Symbol(real=True)
    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2], y), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq <<= algebra.all.of.et.all.split.apply(Eq[-2], cond=y <= M), algebra.all.of.ou.apply(Eq[-1])

    Eq <<= Eq[-2].subs(Eq.eq_max), Eq[-3].this.expr.apply(algebra.any.of.cond.subs, x, (m + y) / 2), Eq[-1].this.find(NotElement).apply(sets.notin_interval.of.ou)

    Eq <<= Eq[-2].this.expr.apply(algebra.any.of.cond.subs, x, (m + M) / 2), algebra.all_et.of.et.all.apply(Eq[-1])

    Eq <<= algebra.et.of.et.apply(Eq[-3]), algebra.all.of.infer.apply(Eq[-2]), algebra.all.of.infer.apply(Eq[-1])

    Eq << sets.lt.then.el.interval.average.apply(Eq[0])

    Eq <<= algebra.all.of.infer.apply(Eq[-3]), Eq[-2].this.rhs * 2, Eq[-1].this.rhs.apply(sets.el.of.el.mul.interval, 2)

    Eq <<= algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq[-3]), Eq[-2].this.rhs - y, Eq[-1].this.rhs.apply(sets.el.of.el.sub, m)

    Eq << Eq[-2].this.lhs.apply(sets.el_interval.then.gt)

    Eq <<= Eq[-3].this.lhs.apply(algebra.lt.gt.then.gt.trans, ret=1), Eq[-1].this.rhs.apply(sets.el.of.et.strengthen, lower=M, strict=True)

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt.gt.then.gt.add), algebra.infer.of.cond.apply(Eq[-1])

    Eq << Eq[-1] + (m - M)

    Eq << Eq[-2].this.rhs * 2





if __name__ == '__main__':
    run()
# created on 2019-08-27
# updated on 2023-05-12
