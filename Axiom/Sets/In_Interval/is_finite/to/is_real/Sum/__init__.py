from util import *


@apply
def apply(el, is_finite):
    γ, domain = el.of(Element)
    fk, (k, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert k.is_integer
    S[0], S[1] = domain.of(Interval)
    assert domain.right_open and domain.left_open

    return Element(Sum[k:oo](γ ** k * fk), Interval(-oo, oo))



@prove
def prove(Eq):
    from Axiom import Algebra, Sets, Calculus

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, left_open=True, right_open=True)), Less(Sup[k:oo](Abs(r[k])), oo))

    Eq << Algebra.All_Le_Sup.apply(Eq[1].find(Sup))

    Eq.gt_zero, Eq.lt = Sets.In_Interval.to.And.apply(Eq[0])

    Eq << Algebra.Gt_0.to.Gt_0.Pow.apply(Eq.gt_zero, k)

    Eq << Algebra.Gt_0.to.Gt_0.Abs.apply(Eq[-1])

    Eq << Algebra.Gt_0.Le.to.Le.Mul.apply(Eq[-1], Eq[-3])

    n = Symbol(integer=True, positive=True)
    Eq << Algebra.Le.to.Le.Sum.apply(Eq[-1], (k, 0, n))

    Eq << Algebra.AbsSum.le.Sum_Abs.apply(Eq[2].find(Sum)._subs(oo, n))

    Eq << Algebra.Le.Le.to.Le.trans.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Gt_0.to.Eq.Abs.apply(Eq.gt_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Algebra.Lt.to.Ne.apply(Eq.lt)

    Eq << Algebra.Ne.to.Eq.Sum.geometric_series.apply(Eq[-1], Eq[-2].rhs.find(Sum))

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Algebra.LeAbs.to.And.apply(Eq[-1])

    Eq <<= Calculus.Le.to.Le.Limit.apply(Eq[-2], (n, oo)), Calculus.Ge.to.Ge.Limit.apply(Eq[-1], (n, oo))

    Eq <<= Eq[-2].this.lhs.apply(Calculus.Limit.eq.Sum), Eq[-1].this.lhs.apply(Calculus.Limit.eq.Sum)

    Eq <<= Eq[-2].this.rhs.apply(Calculus.Limit.eq.Mul), Eq[-1].this.rhs.apply(Calculus.Limit.eq.Mul)

    Eq.upper_bound, Eq.lower_bound = Eq[-2].this.find(Limit).apply(Calculus.Limit.eq.Mul), Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Mul)

    Eq << Algebra.Gt.to.Gt.relax.apply(Eq.gt_zero, -1)

    Eq << Algebra.Gt.Lt.to.Lt.Abs.apply(Eq[-1], Eq.lt)

    Eq << Calculus.LtAbs.to.Eq_0.Limit.geometric_series.apply(Eq[-1], n)

    Eq.upper_bound = Eq.upper_bound.subs(Eq[-1])

    Eq.lower_bound = Eq.lower_bound.subs(Eq[-1])

    Eq << -Eq.lt + 1

    Eq << Algebra.Gt_0.Lt.to.Lt.Div.apply(Eq[-1], Eq[1], simplify=False)

    Eq << -Eq[-1]

    Eq <<= Algebra.Le.Lt.to.Lt.trans.apply(Eq.upper_bound, Eq[-2]), Algebra.Ge.Gt.to.Gt.trans.apply(Eq.lower_bound, Eq[-1])

    Eq << Algebra.Lt.Gt.to.Lt.Abs.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.domain_defined)

    Eq << Sets.Abs_Lt_oo.to.is_real.apply(Eq[-1], simplify=None)





if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-04-16
from . import negative
