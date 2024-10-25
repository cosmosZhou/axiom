from util import *


@apply
def apply(is_nonnegative, lt, left_open=True, right_open=True, x=None):
    m = is_nonnegative.of(Expr >= 0)
    S[m], M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, m ** 2)


@prove
def prove(Eq):
    from axiom import sets, algebra

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m >= 0, m < M, x=x)

    Eq << sets.lt.then.el.interval.average.apply(Eq[1])

    Eq << sets.el_interval.then.et.apply(Eq[-1])

    Eq << algebra.gt.ge.then.gt.trans.apply(Eq[-2], Eq[0])

    Eq.eq_max = algebra.ge_zero.lt.then.eq.max.apply(Eq[0], Eq[1])

    Eq << algebra.ge.lt.then.gt.trans.apply(Eq[0], Eq[1])

    Eq.eq_abs_M = algebra.gt_zero.then.eq.abs.apply(Eq[-1])

    Eq.eq_abs_m = algebra.ge_zero.then.eq.abs.apply(Eq[0])

    Eq << algebra.eq.of.et.squeeze.apply(Eq[2])

    y = Symbol(real=True)
    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2], y), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq <<= algebra.all.of.et.all.split.apply(Eq[-2], cond=y <= M ** 2), algebra.all.of.infer.apply(Eq[-1])

    Eq <<= algebra.all.of.infer.apply(Eq[-3]), Eq[-2].subs(Eq.eq_max), Eq[-1].this.lhs.apply(sets.el_interval.then.gt)

    Eq <<= Eq[-3].this.rhs.apply(algebra.any.of.cond.subs, x, (m + sqrt(y)) / 2), Eq[-2].this.expr.apply(algebra.any.of.cond.subs, x, (M + m) / 2), Eq[-1].this.lhs.apply(algebra.cond.then.infer.et, cond=Eq[0])

    Eq <<= algebra.infer.of.et.infer.apply(Eq[-3]), algebra.et.of.et.apply(Eq[-2]), algebra.infer_infer.of.et.infer.apply(Eq[-1])

    Eq << algebra.cond.of.cond.subs.bool.apply(Eq[-2], cond=Eq[0], invert=True)

    Eq <<= Eq[-5].this.lhs.apply(sets.el_interval.then.gt), Eq[-4].this.rhs.apply(sets.el.of.el.sub, m / 2), Eq[-3].this.expr.apply(algebra.lt.of.gt_zero), Eq[-1].this.lhs.apply(algebra.ge_zero.gt.then.gt.square)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.then.ge.relax)

    Eq <<= Eq[-4].this.rhs.apply(algebra.lt.of.gt_zero), Eq[-3].this.rhs.apply(sets.el.of.el.mul.interval, 2), algebra.all.of.infer.apply(Eq[-2])

    Eq <<= Eq[-3].this.rhs.lhs.apply(algebra.sub.square.to.mul), Eq[-2].this.lhs.apply(sets.el.then.el.sqrt), Eq[-1].this.rhs.lhs.apply(algebra.sub.square.to.mul)

    Eq <<= Eq[-3].this.rhs.apply(algebra.mul_gt_zero.of.et.gt_zero), Eq[-2].subs(Eq.eq_abs_m, Eq.eq_abs_M), Eq[-1].this.rhs.apply(algebra.mul_gt_zero.of.et.gt_zero)

    Eq <<= algebra.infer.of.et.infer.apply(Eq[-3]), Eq[-2].this.rhs.apply(sets.el.of.et.strengthen, M, strict=True), algebra.infer.of.et.infer.apply(Eq[-1])

    Eq <<= Eq[-4].this.rhs * 2, Eq[-5].this.rhs * 2, algebra.infer.of.cond.apply(Eq[-3]), Eq[-1].this.lhs.apply(algebra.gt.then.gt.sqrt), Eq[-2].this.rhs.apply(algebra.add_gt_zero.of.et.gt_zero, 1)

    Eq << Eq[-3] + (m - M)

    Eq <<= Eq[-5].this.lhs.apply(algebra.gt.then.gt.sqrt), Eq[-4].this.rhs.apply(algebra.add_gt_zero.of.et), Eq[-2].subs(Eq.eq_abs_M), algebra.infer.of.et.infer.apply(Eq[-1])

    Eq <<= Eq[-5].subs(Eq.eq_abs_m), Eq[-4].this.lhs.apply(algebra.gt.then.gt.relax, lower=0), Eq[-3].this.rhs.apply(algebra.gt.transport, lhs=slice(1, None)), algebra.infer.of.cond.apply(Eq[-2]), Eq[-1].this.lhs.apply(algebra.gt.then.gt.relax, lower=0)

    Eq << Eq[-4].this.lhs.apply(algebra.gt.then.gt_zero)

    Eq << Eq[-1].this.lhs.apply(algebra.gt_zero.then.gt_zero.sqrt)

    Eq <<= algebra.infer.of.et.infer.apply(Eq[-3]), Eq[-2].this.rhs.apply(algebra.gt.of.et.strengthen, M, strict=True)

    Eq <<= algebra.infer.of.cond.apply(Eq[-2]), Eq[-3].this.rhs / 3, Eq[-1].this.lhs.apply(algebra.gt.then.ge.relax)

    Eq << algebra.infer.of.cond.apply(Eq[-1])

    Eq << Eq[-1] * 2 - M

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2019-07-02
# updated on 2023-05-20
