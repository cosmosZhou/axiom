from util import *


@apply
def apply(el, is_finite):
    λ, domain = el.of(Element)
    S[0], S[1] = domain.of(Interval)
    assert domain.right_open and domain.left_open

    fn, (n, *cond) = is_finite.of(Sup[Abs] < Infinity)
    if cond:
        S[0], S[oo] = cond
    assert n.is_integer
    return Equal(Limit[n:oo](λ ** n * fn), ZeroMatrix(*fn.shape))


@prove
def prove(Eq):
    from axiom import algebra, sets, calculus

    x = Symbol(real=True, shape=(oo,))
    γ = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Element(γ, Interval(0, 1, left_open=True, right_open=True)), Less(Sup[n:oo](Abs(x[n])), oo))

    Eq << algebra.imply.all.le_sup.apply(Eq[1].find(Sup))

    Eq.gt_zero, Eq.lt = sets.el_interval.imply.et.apply(Eq[0])

    Eq << algebra.gt_zero.imply.gt_zero.pow.apply(Eq.gt_zero, n)

    Eq << algebra.gt_zero.imply.gt_zero.abs.apply(Eq[-1])

    Eq << algebra.gt_zero.le.imply.le.mul.apply(Eq[-1], Eq[-3])

    Eq <<  calculus.le.imply.le.limit.apply(Eq[-1], (n, oo))

    Eq.le = Eq[-1].this.rhs.apply(calculus.limit.to.mul)

    Eq << calculus.el_interval.imply.is_zero.limit.geometric_series.positive.apply(Eq[0], n)

    Eq << sets.is_zero.imply.is_real.apply(Eq[-1])

    Eq << calculus.is_limited.imply.eq.abs.limit.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq.le.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.abs)

    Eq << GreaterEqual(Eq[-1].lhs.expr, 0, plausible=True)

    Eq << calculus.ge.imply.ge.limit.apply(Eq[-1], (n, oo))

    Eq << algebra.ge.le.imply.eq.apply(Eq[-1], Eq[-3])

    Eq << calculus.is_zero.imply.is_zero.limit.st.abs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-04-18
from . import negative
