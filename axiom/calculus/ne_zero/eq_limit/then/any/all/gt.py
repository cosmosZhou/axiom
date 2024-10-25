from util import *


@apply
def apply(is_nonzero, eq, delta=None):
    A = is_nonzero.of(Unequal[0])
    assert A.is_real
    fx, (x, x0) = eq.of(Equal[Limit, A])
    if delta is None:
        delta = eq.generate_var(positive=True, var='delta')
    x0, dir = x0.clear_infinitesimal()
    return Any[delta](All[x:(abs(x - x0) > 0) & ((abs(x - x0) < delta))](abs(fx) > abs(A) / 2))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Unequal(A, 0), Equal(Limit[x:x0](f(x)), A))

    Eq << algebra.cond.of.et.infer.split.apply(Eq[2], cond=A > 0)

    Eq.gt, Eq.le = algebra.cond.then.et.infer.split.apply(Eq[1], cond=A > 0)

    Eq << algebra.infer_et.then.infer.et.apply(Eq.gt)

    Eq << Eq[-1].this.rhs.apply(calculus.gt_zero.eq_limit.then.any.all.gt)

    Eq << (A > 0).this.apply(algebra.gt_zero.then.eq.abs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.then.cond.subs, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.gt.then.gt_zero.trans, ret=0)

    Eq << Eq[-1].this.rhs.expr.expr.args[0].apply(algebra.gt_zero.then.eq.abs)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.eq.cond.then.cond.subs, reverse=True)

    Eq << And(A <= 0, Eq[0]).this.apply(algebra.ne_zero.le_zero.then.lt_zero)

    Eq << Eq[-1].this.apply(algebra.infer.fold)

    Eq << algebra.cond.infer.then.cond.trans.apply(Eq[0], Eq[-1])

    Eq <<= Eq.le & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(calculus.lt_zero.eq_limit.then.any.all.lt)

    Eq << (A <= 0).this.apply(algebra.le_zero.then.eq.abs)

    Eq << -Eq[-1].this.rhs

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.cond.then.cond.subs, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.lt.then.lt_zero.trans, ret=0)

    Eq << Eq[-1].this.find(Expr < 0).apply(algebra.lt_zero.then.eq.abs)

    Eq << -Eq[-1].this.find(Equal)

    Eq << Eq[-1].this.rhs.expr.expr.apply(algebra.eq.cond.then.cond.subs, reverse=True)

    Eq << -Eq[-1].this.rhs.expr.expr





if __name__ == '__main__':
    run()
# created on 2020-05-15
# updated on 2023-05-12
