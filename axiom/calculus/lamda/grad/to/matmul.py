from util import *


@apply
def apply(self):
    (fxi, (xi, S[1])), (i, S[0], n) = self.of(Lamda[Derivative])
    x, S[i] = xi.of(Indexed)
    fx = fxi._subs(xi, x)
    return Equal(self, Derivative[x](fx) @ OneMatrix(n))


@prove
def prove(Eq):
    from axiom import calculus

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    i = Symbol(integer=True)
    Eq << apply(Lamda[i:n](Derivative[x[i]](f(x[i]))))

    Eq << Eq[-1].this.rhs.apply(calculus.matmul.grad.to.lamda)










if __name__ == '__main__':
    run()
# created on 2023-03-19
