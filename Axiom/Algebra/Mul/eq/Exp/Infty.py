from util import *


@apply
def apply(self):
    a, X = self.of(Exp * Expr)
    indices, limits = X.variables_with_limits()
    assert X[tuple(indices)] in FiniteSet(0, 1) or \
    X[tuple(indices)].defun() in FiniteSet(0, 1) or \
    X[tuple(indices)].defun().defun() in FiniteSet(0, 1)

    return Equal(self, exp(a + (X - 1) * oo))


@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    p = Function(bool=True)
    a = Symbol(real=True, shape=(n, n))
    i, j = Symbol(integer=True)
    Ξ = Lamda[j:n, i:n](Bool(p(i, j)))
    Eq << apply(Ξ * exp(a))

    Eq << Eq[-1].this.rhs.apply(Algebra.Exp.Infty.eq.Mul)



if __name__ == '__main__':
    run()
# created on 2023-06-18
