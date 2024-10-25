from util import *


@apply
def apply(lt, lt_max, x=None):
    U, maxi = lt_max.of(Less)
    _M, _m = maxi.of(Max[Expr ** 2, Expr ** 2])
    if x is None:
        x = lt.generate_var(real=True)
    m, M = lt.of(Less)
    assert {M, m} == {_M, _m}
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m < M, U < Max(M ** 2, m ** 2))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[-1], cond=M > 0)

    Eq <<= algebra.cond.of.et.infer.split.apply(Eq[-2], cond=m > 0), algebra.cond.of.et.infer.split.apply(Eq[-1], cond=m > 0)

    Eq <<= Eq[-4].this.apply(algebra.infer.flatten), Eq[-3].this.apply(algebra.infer.flatten), Eq[-2].this.apply(algebra.infer.flatten), Eq[-1].this.apply(algebra.infer.flatten)

    Eq <<= algebra.cond.then.infer.et.apply(Eq[0] & Eq[1], cond=Eq[-4].lhs),\
        algebra.cond.then.infer.et.apply(Eq[0] & Eq[1], cond=Eq[-3].lhs),\
        Eq[-2].this.lhs.apply(algebra.le.gt.then.lt.trans),\
        algebra.cond.then.infer.et.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq <<= Eq[-3].this.rhs.apply(algebra.cond.then.et.infer.et.split, cond=M + m > 0), \
        Eq[-1].this.rhs.args[::2].apply(algebra.le_zero.lt.then.eq.max, simplify=None, ret=slice(None)), \
        Eq[-4].this.rhs.args[-1].apply(algebra.gt.then.ge.relax), \
        Eq[-2].this.lhs.apply(algebra.lt.then.le.relax)

    Eq <<= algebra.infer.then.et.infer.apply(Eq[-4], simplify=None), \
        Eq[-3].this.rhs.args[:4:2].apply(algebra.eq.cond.then.cond.subs, simplify=None), \
        Eq[-2].this.rhs.args[::2].apply(algebra.ge_zero.lt.then.eq.max, ret=slice(None)), \
        Eq[-1].this.apply(algebra.infer.contraposition)

    Eq <<= Eq[-5].this.rhs.rhs.apply(algebra.et.then.cond, index=slice(2, None, -2), simplify=None), \
        Eq[-4].this.rhs.rhs.apply(algebra.et.then.cond, index=slice(3, None, -3), simplify=None), \
        Eq[-3].this.rhs.args[:3].apply(algebra.le_zero.lt.lt.then.any.square_gt), \
        Eq[-2].this.rhs.args[::2].apply(algebra.eq.cond.then.cond.subs), \
        algebra.infer.of.cond.apply(Eq[-1]).reversed

    Eq <<= Eq[-3].this.rhs.rhs.args[1].apply(algebra.gt.transport, lhs=0), \
        Eq[-2].this.rhs.rhs.args[2].apply(algebra.le.transport), \
        Eq[-1].this.rhs.apply(algebra.ge_zero.lt.lt.then.any.square_gt)

    Eq <<= Eq[-2].this.rhs.rhs.args[1:].apply(algebra.le_zero.gt.then.eq.max, ret=1), \
        Eq[-1].this.rhs.rhs.args[1:].apply(algebra.gt_zero.le.then.eq.max, ret=0)

    Eq <<= Eq[-2].this.rhs.rhs.args[:2].apply(algebra.eq.cond.then.cond.subs), \
        Eq[-1].this.rhs.rhs.args[:2].apply(algebra.eq.cond.then.cond.subs)

    Eq <<= Eq[-2].this.rhs.apply(algebra.infer_et.then.infer.et), \
        Eq[-1].this.rhs.rhs.args[1].apply(algebra.gt.then.ge.relax)

    Eq.is_positive, Eq.is_nonpositive = Eq[-2].this.rhs.rhs.apply(algebra.le_zero.gt_zero.lt.then.any.square_gt),\
        Eq[-1].this.rhs.apply(algebra.infer_et.then.infer.et)

    Eq <<= Eq.is_nonpositive.this.rhs.rhs.apply(algebra.cond.then.et.infer.split, cond=m + M < 0)

    Eq << Eq[-1].this.rhs.apply(algebra.infer.then.et.infer)

    Eq << algebra.infer.then.et.infer.apply(Eq[-1], simplify=None)

    Eq <<= Eq[-1].this.rhs.rhs.apply(algebra.et.then.cond, index=slice(None, None, 2)), Eq[-2].this.rhs.rhs.apply(algebra.et.then.cond, index=0)

    Eq <<= Eq[-2].this.rhs.apply(algebra.infer_et.then.infer.et), Eq[-1].this.rhs.apply(algebra.infer_et.then.infer.et)

    Eq.is_negative = Eq[-2].this.rhs.rhs.apply(algebra.ge_zero.lt_zero.lt.then.any.square_gt)

    Eq << Eq[-1].this.rhs.rhs.args[0].apply(algebra.eq.transport, lhs=0)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.then.cond.subs, ret=0)

    Eq << algebra.infer_et.then.infer.et.apply(Eq[-1], index=0)

    Eq << Eq[-1].this.rhs.apply(algebra.cond.infer.then.infer.et.rhs)

    Eq << Eq[-1].this.rhs.rhs.args[1:].apply(algebra.gt_zero.lt.then.any.square_gt)

    Eq << Eq[-1].this.rhs.rhs.apply(algebra.eq.cond.then.cond.subs, reverse=True)

    Eq <<= Eq[-1] & Eq.is_negative & Eq.is_positive





if __name__ == '__main__':
    run()
# created on 2019-09-08
# updated on 2023-05-18
