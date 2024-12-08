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
    from Axiom import Sets, Calculus, Algebra

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:a:b](Element(Derivative[x](f(x)), Interval.open(0, oo))), Element(x0, domain), Element(x1, domain), x0 < x1)

    Eq.subset = Sets.In.In.to.Subset.Interval.apply(Eq[1], Eq[2])

    Eq.is_positive_real = Sets.Subset.All.to.All.apply(Eq.subset, Eq[0])

    Eq << Calculus.is_differentiable.to.is_continuous.apply(Eq.is_positive_real)

    Eq << Algebra.Lt.to.Le.relax.apply(Eq[3])

    Eq.any = Calculus.Le.is_continuous.is_differentiable.to.Any.Eq.mean_value_theorem.Lagrange.close.apply(Eq[-1], Eq[-2], Eq.is_positive_real)

    Eq << Eq.is_positive_real.this.expr.apply(Sets.is_positive.to.Gt_0)

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[3])

    Eq << Algebra.Cond.All.to.All.And.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt_0.Gt_0.to.Gt_0)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq.any)

    Eq << Eq[-1].this.expr.apply(Algebra.Gt.Eq.to.Gt.trans)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Gt_0.to.Lt.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-04-30
# updated on 2023-05-14
