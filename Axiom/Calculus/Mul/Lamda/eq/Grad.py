from util import *


@apply
def apply(self, i=None):
    (fxi, (xi, S[1])), (i, S[0], n) = self.of(Identity * Lamda[Derivative])
    x, S[i] = xi.of(Indexed)
    fx = fxi._subs(xi, x)
    return Equal(self, Derivative[x](fx))


@prove
def prove(Eq):
    from Axiom import Calculus

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Identity(n) * Lamda[i:n](Derivative[x[i]](f(x[i]))))

    Eq << Eq[0].this.rhs.apply(Calculus.Grad.eq.Mul.Lamda)










if __name__ == '__main__':
    run()
# created on 2023-03-18
