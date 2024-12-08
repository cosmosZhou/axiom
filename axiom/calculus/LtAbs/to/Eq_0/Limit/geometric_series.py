from util import *


@apply
def apply(lt, n):
    x = lt.of(Abs[Expr] < 1)
    return Equal(Limit[n:oo](x ** n), ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    n = Symbol(integer=True, positive=True)
    γ = Symbol(real=True, given=True)
    Eq << apply(Abs(γ) < 1, n)

    Eq.gt_zero, Eq.le_zero = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=γ > 0)

    Eq.lt_zero, Eq.is_zero = Algebra.Imply.of.And.Imply.split.apply(Eq.le_zero, cond=γ < 0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq.is_zero)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.LtAbs.to.Lt)

    Eq << Eq[-1].this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Eq[-1].this.lhs.apply(Calculus.In_Interval.to.Eq_0.Limit.geometric_series.positive, n)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(Algebra.LtAbs.to.Gt)

    Eq << Eq[-1].this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Eq[-1].this.lhs.apply(Calculus.In_Interval.to.Eq_0.Limit.geometric_series.negative, n)





if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-20
