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
    from axiom import algebra, sets, calculus

    r = Symbol(shape=(oo,), real=True)
    γ = Symbol(real=True)
    k = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, left_open=True, right_open=True)), Less(Sup[k:oo](Abs(r[k])), oo))

    Eq << algebra.then.all.le_sup.apply(Eq[1].find(Sup))

    Eq.gt_zero, Eq.lt = sets.el_interval.then.et.apply(Eq[0])

    Eq << algebra.gt_zero.then.gt_zero.pow.apply(Eq.gt_zero, k)

    Eq << algebra.gt_zero.then.gt_zero.abs.apply(Eq[-1])

    Eq << algebra.gt_zero.le.then.le.mul.apply(Eq[-1], Eq[-3])

    n = Symbol(integer=True, positive=True)
    Eq << algebra.le.then.le.sum.apply(Eq[-1], (k, 0, n))

    Eq << algebra.then.abs_le.sum.abs.apply(Eq[2].find(Sum)._subs(oo, n))

    Eq << algebra.le.le.then.le.trans.apply(Eq[-1], Eq[-2])

    Eq << algebra.gt_zero.then.eq.abs.apply(Eq.gt_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << algebra.lt.then.ne.apply(Eq.lt)

    Eq << algebra.ne.then.eq.sum.geometric_series.apply(Eq[-1], Eq[-2].rhs.find(Sum))

    Eq << Eq[-3].subs(Eq[-1])

    Eq << algebra.abs_le.then.et.apply(Eq[-1])

    Eq <<= calculus.le.then.le.limit.apply(Eq[-2], (n, oo)), calculus.ge.then.ge.limit.apply(Eq[-1], (n, oo))

    Eq <<= Eq[-2].this.lhs.apply(calculus.limit.to.sum), Eq[-1].this.lhs.apply(calculus.limit.to.sum)

    Eq <<= Eq[-2].this.rhs.apply(calculus.limit.to.mul), Eq[-1].this.rhs.apply(calculus.limit.to.mul)

    Eq.upper_bound, Eq.lower_bound = Eq[-2].this.find(Limit).apply(calculus.limit.to.mul), Eq[-1].this.find(Limit).apply(calculus.limit.to.mul)

    Eq << algebra.gt.then.gt.relax.apply(Eq.gt_zero, -1)

    Eq << algebra.gt.lt.then.lt.abs.apply(Eq[-1], Eq.lt)

    Eq << calculus.abs_lt.then.is_zero.limit.geometric_series.apply(Eq[-1], n)

    Eq.upper_bound = Eq.upper_bound.subs(Eq[-1])

    Eq.lower_bound = Eq.lower_bound.subs(Eq[-1])

    Eq << -Eq.lt + 1

    Eq << algebra.gt_zero.lt.then.lt.div.apply(Eq[-1], Eq[1], simplify=False)

    Eq << -Eq[-1]

    Eq <<= algebra.le.lt.then.lt.trans.apply(Eq.upper_bound, Eq[-2]), algebra.ge.gt.then.gt.trans.apply(Eq.lower_bound, Eq[-1])

    Eq << algebra.lt.gt.then.lt.abs.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.domain_defined)

    Eq << sets.abs_lt_oo.then.is_real.apply(Eq[-1], simplify=None)





if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-04-16
from . import negative
