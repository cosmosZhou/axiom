from util import *


@apply
def apply(m_is_nonnegative, lt_mM, lt, x=None):
    m = m_is_nonnegative.of(Expr >= 0)
    S[m], M = lt_mM.of(Less)

    U, M2 = lt.of(Less)
    _M = M2.of(Expr ** 2)
    assert _M == M or _M == -M
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from axiom import algebra, sets

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m >= 0, m < M, U < M ** 2)

    x = Eq[-1].variable
    Eq.ge, Eq.lt = algebra.cond.of.et.infer.split.apply(Eq[-1], cond=U >= m ** 2)

    Eq << algebra.lt.ge.then.gt.trans.apply(Eq[1], Eq[0])

    Eq << Eq.lt.this.rhs.apply(algebra.any.of.cond.subs, x, (m + M) / 2)

    Eq.gt, Eq.contains = algebra.infer.of.et.infer.apply(Eq[-1])

    Eq << Eq[1].reversed + m

    Eq << Eq[-1] / 2

    Eq << algebra.ge_zero.gt.then.gt.square.apply(Eq[0], Eq[-1])

    Eq << algebra.cond.then.infer.et.apply(Eq[-1], cond=U < m ** 2)

    Eq << Eq[-1].this.rhs.apply(algebra.gt.lt.then.gt.trans)

    Eq << algebra.infer.of.cond.apply(Eq.contains)

    Eq << sets.lt.then.el.interval.average.apply(Eq[1])

    Eq << Eq.ge.this.rhs.apply(algebra.any.of.cond.subs, x, (sqrt(U) + M) / 2)

    Eq << Eq[-1].this.find(Element).apply(sets.el_interval.of.et)

    Eq << algebra.infer.of.et.infer.apply(Eq[-1], index=None)

    Eq <<= Eq[-1].this.rhs.apply(algebra.gt.of.gt_zero), Eq[-3].this.rhs.apply(algebra.lt.transport, lhs=0)

    Eq <<= Eq[-2].this.find(Add).apply(algebra.sub.square.to.mul), Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.lhs.apply(algebra.ge.then.ge.relax, lower=0), Eq[-1].this.lhs.apply(algebra.ge.then.ge.relax, lower=0)

    Eq.is_nonnegative = Eq[-2].this.rhs.apply(algebra.mul_gt_zero.of.et.gt_zero)

    Eq <<= algebra.cond.then.infer.et.apply(Eq[2], cond=U >= 0)

    Eq << Eq[-1].this.rhs.apply(algebra.ge_zero.lt.then.lt.sqrt)

    Eq << algebra.gt_zero.then.eq.abs.apply(Eq[4])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.infer.of.et.infer.apply(Eq.is_nonnegative)

    Eq <<= Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.rhs.apply(algebra.add_gt_zero.of.et, 0), Eq[-1].this.rhs.apply(algebra.gt_zero.of.gt)

    Eq <<= Eq[-2].this.rhs.args[1] / 3, Eq[-1].this.rhs.reversed

    Eq <<= algebra.infer.of.et.infer.apply(Eq[-1])

    Eq <<= algebra.infer.of.cond.apply(Eq[-2])

    Eq <<= Eq[-1].this.lhs.apply(algebra.ge_zero.then.ge_zero.sqrt)

    Eq << algebra.cond.then.infer.et.apply(Eq[1].reversed, cond=U >= m ** 2)

    Eq << Eq[-1].this.rhs.args[1].apply(algebra.ge.then.ge.sqrt)

    Eq << algebra.ge_zero.then.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.gt.ge.then.gt.add)

    Eq << Eq[-1].this.rhs / 2





if __name__ == '__main__':
    run()
# created on 2019-07-07
# updated on 2023-05-20
