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
    from Axiom import Algebra, Calculus

    x, x0, A = Symbol(real=True)
    f = Function(real=True)
    Eq << apply(Unequal(A, 0), Equal(Limit[x:x0](f(x)), A))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[2], cond=A > 0)

    Eq.gt, Eq.le = Algebra.Cond.to.And.Imply.split.apply(Eq[1], cond=A > 0)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq.gt)

    Eq << Eq[-1].this.rhs.apply(Calculus.Gt_0.Eq_Limit.to.Any.All.Gt)

    Eq << (A > 0).this.apply(Algebra.Gt_0.to.Eq.Abs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Algebra.Gt.to.Gt_0.trans, ret=0)

    Eq << Eq[-1].this.rhs.expr.expr.args[0].apply(Algebra.Gt_0.to.Eq.Abs)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq << And(A <= 0, Eq[0]).this.apply(Algebra.Ne_0.Le_0.to.Lt_0)

    Eq << Eq[-1].this.apply(Algebra.Imply.fold)

    Eq << Algebra.Cond.Imply.to.Cond.trans.apply(Eq[0], Eq[-1])

    Eq <<= Eq.le & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Calculus.Lt_0.Eq_Limit.to.Any.All.Lt)

    Eq << (A <= 0).this.apply(Algebra.Le_0.to.Eq.Abs)

    Eq << -Eq[-1].this.rhs

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Algebra.Lt.to.Lt_0.trans, ret=0)

    Eq << Eq[-1].this.find(Expr < 0).apply(Algebra.Lt_0.to.Eq.Abs)

    Eq << -Eq[-1].this.find(Equal)

    Eq << Eq[-1].this.rhs.expr.expr.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True)

    Eq << -Eq[-1].this.rhs.expr.expr





if __name__ == '__main__':
    run()
# created on 2020-05-15
# updated on 2023-05-12
