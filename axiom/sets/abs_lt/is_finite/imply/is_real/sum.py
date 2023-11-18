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
    from axiom import algebra, sets

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Abs(γ) < 1, Less(Sup[k:oo](Abs(r[k])), oo))

    Eq.gt_zero, Eq.le_zero = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=γ > 0)

    Eq.lt_zero, Eq.is_zero = algebra.infer.given.et.infer.split.apply(Eq.le_zero, cond=γ < 0)

    Eq << algebra.infer.given.infer.subs.apply(Eq.is_zero)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.find(Sum)().expr.simplify()

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(algebra.abs_lt.imply.lt)

    Eq << Eq[-1].this.lhs.apply(sets.lt.gt.imply.el.interval)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.is_finite.imply.is_real.sum, simplify=None)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(algebra.abs_lt.imply.gt)

    Eq << Eq[-1].this.lhs.apply(sets.lt.gt.imply.el.interval)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(sets.el_interval.is_finite.imply.is_real.sum.negative, simplify=None)




if __name__ == '__main__':
    run()
# created on 2023-04-16
# updated on 2023-05-15
