from util import *


@apply
def apply(contains0, contains1, all_is_positive):
    x0, domain = contains0.of(Element)
    x1, S[domain] = contains1.of(Element)
    a, b = domain.of(Interval)
    (fx, (x, S[2])), (S[x], S[a], S[b]) = all_is_positive.of(All[Derivative > 0])
    assert domain.is_open
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import is_differentiable
    f = lambda t: fx._subs(x, t)
    return is_differentiable(f, x0, x1, open=False)


@prove
def prove(Eq):
    from axiom import calculus, sets

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(Element(x0, domain), Element(x1, domain), All[x:domain](Derivative(f(x), (x, 2)) > 0))

    Eq << calculus.all_gt_zero.then.is_differentiable.apply(Eq[2])

    Eq << sets.el.el.then.subset.interval.apply(Eq[0], Eq[1])

    Eq << sets.subset.all.then.all.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2020-05-05
