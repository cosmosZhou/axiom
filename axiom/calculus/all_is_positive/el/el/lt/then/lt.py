from util import *


@apply
def apply(all_is_positive_real, contains0, contains1, le):
    ((fx, (x, S[1])), R), (S[x], a, b) = all_is_positive_real.of(All[Element[Derivative]])
    assert R in Interval.open(0, oo)
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
    Eq << apply(All[x:a:b](Element(Derivative[x](f(x)), Interval.open(0, oo))), Element(x0, domain), Element(x1, domain), x0 < x1)

    Eq.subset = sets.el.el.then.subset.interval.apply(Eq[1], Eq[2])

    Eq.is_positive_real = sets.subset.all.then.all.apply(Eq.subset, Eq[0])

    Eq << calculus.is_differentiable.then.is_continuous.apply(Eq.is_positive_real)

    Eq << algebra.lt.then.le.relax.apply(Eq[3])

    Eq.any = calculus.le.is_continuous.is_differentiable.then.any.eq.mean_value_theorem.Lagrange.close.apply(Eq[-1], Eq[-2], Eq.is_positive_real)

    Eq << Eq.is_positive_real.this.expr.apply(sets.is_positive.then.gt_zero)

    Eq << algebra.lt.then.gt_zero.apply(Eq[3])

    Eq << algebra.cond.all.then.all.et.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(algebra.gt_zero.gt_zero.then.gt_zero)

    Eq << algebra.all.any.then.any.et.apply(Eq[-1], Eq.any)

    Eq << Eq[-1].this.expr.apply(algebra.gt.eq.then.gt.trans)

    Eq << algebra.et.then.et.apply(Eq[-1])

    Eq << algebra.gt_zero.then.lt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-04-30
# updated on 2023-05-14
