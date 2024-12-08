from util import *


@apply
def apply(lt, is_finite):
    λ = lt.of(Abs < 1)
    fn, (n, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    return Equal(Limit[n:oo](λ ** n * fn), ZeroMatrix(*fn.shape))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    x = Symbol(real=True, shape=(oo,))
    λ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Abs(λ) < 1, Less(Sup[n:oo](Abs(x[n])), oo, evaluate=False))

    Eq.gt_zero, Eq.le_zero = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=λ > 0)

    Eq.lt_zero, Eq.is_zero = Algebra.Imply.of.And.Imply.split.apply(Eq.le_zero, cond=λ < 0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq.is_zero)

    Eq << Eq[-1].this.find(Limit)().expr.simplify()

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.LtAbs.to.Lt)

    Eq << Eq[-1].this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Calculus.In_Interval.is_finite.to.Eq_0.Limit)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(Algebra.LtAbs.to.Gt)

    Eq << Eq[-1].this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Calculus.In_Interval.is_finite.to.Eq_0.Limit.negative)





if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-15
