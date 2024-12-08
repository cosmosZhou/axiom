from util import *


@apply
def apply(self, n=None, k=None):
    fx, (x, a, b) = self.of(Integral)
    if n is None:
        n = self.generate_var(integer=True, var='n')

    if k is None:
        k = self.generate_var(n, integer=True, var='k')
    assert fx.is_continuous_at(x)
    return Equal(self, (b - a) * Limit[n:oo](Sum[k:n](fx._subs(x, a + (b - a) * k / n)) / n))


@prove
def prove(Eq):
    from Axiom import Algebra, Calculus

    x, a, b = Symbol(real=True)
    f = Function(real=True, continuous=True)
    Eq << apply(Integral[x:a:b](f(x)))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=a < b)

    Eq << (a < b).this.apply(Calculus.Lt.to.Integral.eq.Mul.Limit.Maxima.Darboux, Eq[0].lhs)

    Eq << (a < b).this.apply(Calculus.Lt.to.Integral.eq.Mul.Limit.Minima.Darboux, Eq[0].lhs)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.trans)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Lt.to.Gt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Eq.to.Eq.Div)

    Eq << Algebra.Imply_And.to.Imply.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Calculus.Lt.Eq_Limit.to.Eq.Darboux)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[2], cond=a > b)

    Eq <<= Eq[-2].this.apply(Algebra.Imply.flatten), Eq[-1].this.apply(Algebra.Imply.flatten)

    Eq << Eq[-2].this.lhs.apply(Calculus.Gt.to.Integral.eq.Limit.Riemann, Eq[0].lhs)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-06-08
