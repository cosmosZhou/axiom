from util import *


@apply
def apply(lt, self, n=None, k=None):
    a, b = lt.of(Less)
    fx, (x, S[a], S[b]) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert fx.is_continuous_at(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from Axiom import Calculus, Algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(a < b, Integral[x:a:b](f(x)))

    Eq << Calculus.Lt.to.Integral.eq.Mul.Limit.Maxima.Darboux.apply(Eq[0], Eq[1].lhs)

    Eq << Calculus.Lt.to.Integral.eq.Mul.Limit.Minima.Darboux.apply(Eq[0], Eq[1].lhs)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt.to.Gt_0.apply(Eq[0])

    Eq << Algebra.Gt_0.Eq.to.Eq.Div.apply(Eq[-1], Eq[-2])

    Eq << Calculus.Lt.Eq_Limit.to.Eq.Darboux.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-05-27
