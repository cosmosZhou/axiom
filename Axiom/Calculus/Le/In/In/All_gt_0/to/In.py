from util import *


@apply
def apply(le, contains0, contains1, all_is_positive):
    (fx, (x, d)), (S[x], a, b) = all_is_positive.of(All[Derivative > 0])
    x0, domain = contains0.of(Element)
    x1, S[domain] = contains1.of(Element)
    assert domain.is_open
    S[a], S[b] = domain.of(Interval)

    S[x0], S[x1] = le.of(LessEqual)

    d -= 1
    if d:
        fx = Derivative(fx, (x, d))

    f = lambda t: fx._subs(x, t)
    return f(x0) <= f(x1)


@prove(proved=False)
def prove(Eq):
    from Axiom import Sets, Calculus, Algebra

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(x0 <= x1, Element(x0, domain), Element(x1, domain), All[x:domain](Derivative[x](f(x)) > 0))

    Eq << Eq[3].this.expr.apply(Sets.Gt.to.is_extended_real)

    Eq.subset = Sets.In.In.to.Subset.Interval.apply(Eq[1], Eq[2])

    Eq << Sets.Subset.All.to.All.apply(Eq.subset, Eq[-1], simplify=None)

    Eq << Calculus.is_differentiable.to.is_continuous.apply(Eq[-1])

    Eq.any = Calculus.Le.is_continuous.is_differentiable.to.Any.Eq.mean_value_theorem.Lagrange.close.apply(Eq[0], Eq[-1], Eq[-2])

    Eq << Sets.Subset.All.to.All.apply(Eq.subset, Eq[3])

    Eq << Sets.All.to.All.And.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].this.find(Unequal).apply(Sets.Interval_Ne_EmptySet.to.Ge_0, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.Ge_0.Gt_0.to.Ge_0)

    Eq << Algebra.All.Any.to.Any.And.apply(Eq[-1], Eq.any)

    Eq << Eq[-1].this.expr.apply(Algebra.Ge.Eq.to.Ge.trans)

    Eq << Algebra.And.to.And.apply(Eq[-1])

    Eq << Algebra.Ge_0.to.Le.apply(Eq[-2])





if __name__ == '__main__':
    run()
# created on 2020-05-10
# updated on 2023-05-04
