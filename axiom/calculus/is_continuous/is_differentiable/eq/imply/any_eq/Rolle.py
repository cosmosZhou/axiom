from util import *


@apply
def apply(is_continuous, is_differentiable, equal):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import of_continuous, of_differentiable
    fz, (z, a, b) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable)

    assert a < b
    S[fz._subs(z, a)], S[fz._subs(z, b)] = equal.of(Equal)

    return Any[z:a:b](Equal(Derivative(fz, z), 0))


@prove
def prove(Eq):
    from axiom import calculus

    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    a = Symbol(real=True)
    b = Symbol(domain=Interval.open(a, oo))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b), Equal(f(a), f(b)))

    Eq << Less(a, b, plausible=True)

    Eq << calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle.apply(Eq[-1], Eq[0], Eq[1], Eq[2])


if __name__ == '__main__':
    run()

# created on 2020-06-16
