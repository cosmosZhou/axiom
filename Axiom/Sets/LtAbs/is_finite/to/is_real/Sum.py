from util import *


@apply
def apply(lt, is_finite):
    γ = lt.of(Abs < 1)
    fk, (k, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert k.is_integer
    return Element(Sum[k:oo](γ ** k * fk), Interval(-oo, oo))



@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Abs(γ) < 1, Less(Sup[k:oo](Abs(r[k])), oo))

    Eq.gt_zero, Eq.le_zero = Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=γ > 0)

    Eq.lt_zero, Eq.is_zero = Algebra.Imply.of.And.Imply.split.apply(Eq.le_zero, cond=γ < 0)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq.is_zero)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.find(Sum)().expr.simplify()

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(Algebra.LtAbs.to.Lt)

    Eq << Eq[-1].this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Sets.In_Interval.is_finite.to.is_real.Sum, simplify=None)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(Algebra.LtAbs.to.Gt)

    Eq << Eq[-1].this.lhs.apply(Sets.Lt.Gt.to.In.Interval)

    Eq << Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Sets.In_Interval.is_finite.to.is_real.Sum.negative, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-05-15
