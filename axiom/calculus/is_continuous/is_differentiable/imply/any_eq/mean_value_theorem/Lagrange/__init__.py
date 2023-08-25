from util import *


@apply
def apply(is_continuous, is_differentiable):
    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import of_differentiable, of_continuous
    fz, (z, a, b) = of_continuous(is_continuous)
    S[fz], S[(z, a, b)] = of_differentiable(is_differentiable)
    assert a < b

    fa = fz._subs(z, a)
    fb = fz._subs(z, b)

    return Any[z:Interval(a, b, left_open=True, right_open=True)](Equal(fb - fa, (b - a) * Derivative(fz, z)))


@prove
def prove(Eq):
    from axiom import calculus

    from axiom.calculus.lt.is_continuous.is_differentiable.eq.imply.any_eq.Rolle import is_differentiable
    from axiom.calculus.all_eq.imply.all.any.eq.intermediate_value_theorem import is_continuous
    a = Symbol(real=True)
    b = Symbol(domain=Interval.open(a, oo))
    f = Function(shape=(), real=True)
    Eq << apply(is_continuous(f, a, b), is_differentiable(f, a, b))

    Eq << Less(a, b, plausible=True)

    Eq << calculus.lt.is_continuous.is_differentiable.imply.any_eq.mean_value_theorem.Lagrange.apply(Eq[-1], Eq[0], Eq[1])






































if __name__ == '__main__':
    run()


from . import close
# created on 2020-06-17
