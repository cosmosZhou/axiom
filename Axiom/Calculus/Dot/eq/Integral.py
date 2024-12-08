from util import *


@apply
def apply(self, i=None):
    lhs, (rhs, *limits_i) = self.of(Expr @ Integral)
    vars_i = [v for v, *_ in limits_i]
    assert not lhs.has(*vars_i)
    return Equal(self, Integral(lhs @ rhs, *limits_i))


@prove
def prove(Eq):
    from Axiom import Discrete, Calculus

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    A = Symbol(real=True, shape=(n, n))
    Eq << apply(A @ Integral[x](f(x)))

    Eq << Eq[-1].this.rhs.expr.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Lamda)

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Sum)

    Eq << Eq[-1].this.rhs.find(Integral).apply(Calculus.Integral.eq.Mul)


if __name__ == '__main__':
    run()
# created on 2023-04-08
