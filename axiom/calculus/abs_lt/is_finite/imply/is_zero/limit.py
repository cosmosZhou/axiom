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
    from axiom import algebra, sets, calculus

    x = Symbol(real=True, shape=(oo,))
    λ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Abs(λ) < 1, Less(Sup[n:oo](Abs(x[n])), oo, evaluate=False))

    Eq.gt_zero, Eq.le_zero = algebra.cond.given.et.infer.split.apply(Eq[-1], cond=λ > 0)

    Eq.lt_zero, Eq.is_zero = algebra.infer.given.et.infer.split.apply(Eq.le_zero, cond=λ < 0)

    Eq << algebra.infer.given.infer.subs.apply(Eq.is_zero)

    Eq << Eq[-1].this.find(Limit)().expr.simplify()

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.find(And[~Less]).apply(algebra.abs_lt.imply.lt)

    Eq << Eq[-1].this.lhs.apply(sets.lt.gt.imply.el.interval)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(calculus.el_interval.is_finite.imply.is_zero.limit)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[0], Eq.lt_zero)

    Eq << Eq[-1].this.find(Abs < 1).apply(algebra.abs_lt.imply.gt)

    Eq << Eq[-1].this.lhs.apply(sets.lt.gt.imply.el.interval)

    Eq << algebra.cond.infer.given.et.infer.et.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].this.lhs.apply(calculus.el_interval.is_finite.imply.is_zero.limit.negative)





if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-15
