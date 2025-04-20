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
    from Axiom import Algebra, Set, Calculus, Logic

    x = Symbol(real=True, shape=(oo,))
    λ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Abs(λ) < 1, Less(Sup[n:oo](Abs(x[n])), oo, evaluate=False))

    Eq.gt_zero, Eq.le_zero = Logic.Cond.given.And.Imp.split.apply(Eq[-1], cond=λ > 0)

    Eq.lt_zero, Eq.is_zero = Logic.Imp.given.And.Imp.split.apply(Eq.le_zero, cond=λ < 0)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq.is_zero)

    Eq << Eq[-1].this.find(Limit)().expr.simplify()

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.Lt.of.LtAbs)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Icc.of.Lt.Gt)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq_0.Limit.of.Mem_Icc.IsFinite)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(Algebra.Gt.of.LtAbs)

    Eq << Eq[-1].this.lhs.apply(Set.Mem.Icc.of.Lt.Gt)

    Eq << Logic.Cond.Imp.given.And.Imp.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Calculus.Eq_0.Limit.of.Mem_Icc.IsFinite.negative)





if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-15
