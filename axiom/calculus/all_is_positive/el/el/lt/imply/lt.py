from util import *


@apply
def apply(all_is_positive_real, contains0, contains1, le):
    ((fx, (x, S[1])), R), (S[x], a, b) = all_is_positive_real.of(All[Element[Derivative]])
    assert R in Interval(0, oo, left_open=True)
    x0, domain = contains0.of(Element)
    assert domain.is_open
    S[a], S[b] = domain.of(Interval)

    x1, S[domain] = contains1.of(Element)

    S[x0], S[x1] = le.of(Less)

    f = lambda t: fx._subs(x, t)
    return f(x0) < f(x1)


@prove
def prove(Eq):
    from axiom import sets, calculus, algebra

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:a:b](Element(Derivative[x](f(x)), Interval(0, oo, left_open=True))), Element(x0, domain), Element(x1, domain), x0 < x1)

    Eq.subset = sets.el.el.imply.subset.interval.apply(Eq[1], Eq[2])

    Eq.is_positive_real = sets.subset.all.imply.all.apply(Eq.subset, Eq[0])

    Eq << calculus.is_differentiable.imply.is_continuous.apply(Eq.is_positive_real)

    Eq << algebra.lt.imply.le.relax.apply(Eq[3])

    Eq.any = calculus.le.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.close.apply(Eq[-1], Eq[-2], Eq.is_positive_real)

    Eq << Eq.is_positive_real.this.expr.apply(sets.is_positive.imply.gt_zero)

    Eq << algebra.lt.imply.gt_zero.apply(Eq[3])

    Eq << algebra.cond.all.imply.all_et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.gt_zero.gt_zero.imply.gt_zero)

    Eq << algebra.all.any.imply.any_et.apply(Eq[-1], Eq.any)

    Eq << Eq[-1].this.expr.apply(algebra.gt.eq.imply.gt.transit)

    Eq << algebra.et.imply.et.apply(Eq[-1])

    Eq << algebra.gt_zero.imply.lt.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2020-04-30
# updated on 2023-05-14
