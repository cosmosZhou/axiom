from util import *


@apply
def apply(is_positive, left_open=True, right_open=True, x=None):
    M = is_positive.of(Expr > 0)
    if x is None:
        x = M.generate_var(real=True)

    self = Inf[x:Interval(0, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, 0)


@prove
def prove(Eq):
    from axiom import algebra, sets

    M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(M > 0, x=x)

    Eq << algebra.gt_zero.then.eq.abs.apply(Eq[0])

    Eq << algebra.eq.of.et.squeeze.apply(Eq[1])

    t = Symbol(real=True)
    Eq <<= algebra.inf_le.of.all_any_lt.apply(Eq[-2], t), algebra.inf_ge.of.all.ge.apply(Eq[-1])

    Eq << algebra.all.of.et.all.split.apply(Eq[-1], cond=t <= M ** 2)

    Eq <<= Eq[-2].this.expr.apply(algebra.any.of.cond.subs, x, sqrt(t) / 2)

    Eq <<= Eq[-1].this.find(Less).apply(algebra.lt.of.gt_zero), Eq[-2].this.expr.apply(algebra.any.of.cond.subs, x, M / 2)

    Eq <<= Eq[-2].this.find(Greater) * Rational(4, 3), Eq[-1].this.args[0].apply(sets.el_interval.of.et)

    Eq <<= algebra.all_et.of.et.all.apply(Eq[-2]), Eq[-1].this.args[0].apply(algebra.lt.of.gt_zero)

    Eq <<= algebra.all.of.ou.apply(Eq[-3]), Eq[-2].this.expr.apply(sets.el_interval.of.et), algebra.et.of.et.apply(Eq[-1])

    Eq <<= Eq[-4].this.args[1].apply(sets.notin_interval.of.ou)

    Eq <<= algebra.all.of.infer.apply(Eq[-3]), Eq[-2] * 2, algebra.all.of.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(sets.el_interval.then.et), Eq[-1].this.rhs * 4

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt_zero.le.then.le.sqrt, ret=0), Eq[-1].this.rhs.reversed

    Eq <<= Eq[-2].subs(Eq[2]), Eq[-1].this.lhs.apply(algebra.gt.then.gt.relax, lower=0, ret=0)

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.gt_zero.then.gt_zero.sqrt), Eq[-1].this.lhs.args[0].apply(algebra.gt_zero.then.gt.scale, 4)

    Eq <<= Eq[-1].this.lhs.apply(algebra.gt.gt.then.gt.trans)

    Eq <<= algebra.infer.of.et.infer.apply(Eq[-2])

    Eq <<= Eq[-2].this.lhs.args[0].apply(algebra.gt_zero.then.lt.scale, S.One / 2), algebra.infer_et.of.infer.delete.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(algebra.le.lt.then.lt.trans)

    Eq <<= Eq[-1].this.lhs / 2


if __name__ == '__main__':
    run()
# created on 2019-08-15
