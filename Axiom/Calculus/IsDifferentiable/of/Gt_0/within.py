from util import *


@apply
def apply(is_positive, x0, x1, x=None):
    fx, (x_, d) = is_positive.of(Derivative > 0)
    assert d == 2
    domain = x_.domain
    assert x0.domain == domain == x1.domain
    from Axiom.Calculus.Any.Eq.Rolle.of.Lt.IsContinuous.IsDifferentiable.Eq import is_differentiable
    f = lambda x: fx._subs(x_, x)
    return is_differentiable(f, x0, x1, open=False, x=x)


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    a, b = Symbol(real=True)
    f = Function(real=True)

    x, x0, x1 = Symbol(domain=Interval(a, b, left_open=True, right_open=True))
    Eq << apply(Derivative(f(x), (x, 2)) > 0, x0, x1)

    Eq << Algebra.All.of.Cond.apply(Eq[0], x)

    Eq << Calculus.IsDifferentiable.of.All_Gt_0.apply(Eq[-1])

    Eq << Algebra.All.of.All.limits.restrict.apply(Eq[-1], domain=Interval(x0, x1))


if __name__ == '__main__':
    run()
# created on 2020-05-06
