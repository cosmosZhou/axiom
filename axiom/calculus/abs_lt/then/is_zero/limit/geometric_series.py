from util import *


@apply
def apply(lt, n):
    x = lt.of(Abs[Expr] < 1)
    return Equal(Limit[n:oo](x ** n), ZeroMatrix(*x.shape))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    n = Symbol(integer=True, positive=True)
    γ = Symbol(real=True, given=True)
    Eq << apply(Abs(γ) < 1, n)

    Eq.gt_zero, Eq.le_zero = algebra.cond.of.et.infer.split.apply(Eq[-1], cond=γ > 0)

    Eq.lt_zero, Eq.is_zero = algebra.infer.of.et.infer.split.apply(Eq.le_zero, cond=γ < 0)

    Eq << algebra.infer.of.infer.subs.apply(Eq.is_zero)

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(algebra.abs_lt.then.lt)

    Eq << Eq[-1].this.lhs.apply(sets.lt.gt.then.el.interval)

    Eq << Eq[-1].this.lhs.apply(calculus.el_interval.then.is_zero.limit.geometric_series.positive, n)

    Eq << algebra.cond.infer.of.et.infer.et.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(algebra.abs_lt.then.gt)

    Eq << Eq[-1].this.lhs.apply(sets.lt.gt.then.el.interval)

    Eq << Eq[-1].this.lhs.apply(calculus.el_interval.then.is_zero.limit.geometric_series.negative, n)





if __name__ == '__main__':
    run()
# created on 2023-04-15
# updated on 2023-05-20
