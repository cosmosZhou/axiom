from util import *


@apply
def apply(all_is_positive, contains0, contains1):
    (fx, (x, S[2])), (S[x], a, b) = all_is_positive.of(All[Derivative > 0])

    x0, domain = contains0.of(Element)
    S[a], S[b] = domain.of(Interval)
    assert domain.is_open

    x1, S[domain] = contains1.of(Element)

    from Axiom.Calculus.Lt.is_continuous.is_differentiable.Eq.to.Any.Eq.Rolle import is_differentiable
    f = lambda t: fx._subs(x, t)
    return is_differentiable(f, x0, x1, open=False)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    a, b, x, x0, x1 = Symbol(real=True)
    f = Function(real=True)
    domain = Interval(a, b, left_open=True, right_open=True)
    Eq << apply(All[x:domain](Derivative(f(x), (x, 2)) > 0), Element(x0, domain), Element(x1, domain))

    Eq << Calculus.All_Gt_0.to.is_differentiable.apply(Eq[0])

    x0_ = Symbol('x0', domain=domain)
    x1_ = Symbol('x1', domain=domain)
    Eq << Algebra.All.to.All.limits.restrict.apply(Eq[-1], domain=Interval(x0_, x1_))

    Eq << Eq[-1].subs(x1_, x1)

    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].subs(x0_, x0)
    Eq << Algebra.Cond.Or.to.Cond.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-03-30
