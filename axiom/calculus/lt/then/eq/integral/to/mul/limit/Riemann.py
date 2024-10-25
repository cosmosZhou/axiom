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
    from axiom import calculus, algebra

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(a < b, Integral[x:a:b](f(x)))

    Eq << calculus.lt.then.eq.integral.to.mul.limit.maxima.Darboux.apply(Eq[0], Eq[1].lhs)

    Eq << calculus.lt.then.eq.integral.to.mul.limit.minima.Darboux.apply(Eq[0], Eq[1].lhs)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-2], Eq[-1])

    Eq << algebra.lt.then.gt_zero.apply(Eq[0])

    Eq << algebra.gt_zero.eq.then.eq.div.apply(Eq[-1], Eq[-2])

    Eq << calculus.lt.eq_limit.then.eq.Darboux.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-05-27
