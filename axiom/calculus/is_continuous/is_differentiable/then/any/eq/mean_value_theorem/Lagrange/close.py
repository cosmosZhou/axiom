from util import *


@apply
def apply(is_continuous, is_differentiable):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import of_differentiable, of_continuous
    fz, (z, a, b) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable, open=False)

    assert a <= b

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from axiom import calculus

    from axiom.calculus.lt.is_continuous.is_differentiable.eq.then.any.eq.Rolle import is_differentiable
    from axiom.calculus.all_eq.then.all.any.eq.intermediate_value_theorem import is_continuous
    a = Symbol(real=True)
    b = Symbol(domain=Interval(a, oo))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b, open=False))

    Eq << LessEqual(a, b, plausible=True)

    Eq << calculus.le.is_continuous.is_differentiable.then.any.eq.mean_value_theorem.Lagrange.close.apply(Eq[-1], Eq[0], Eq[1])


if __name__ == '__main__':
    run()
# created on 2020-06-17
