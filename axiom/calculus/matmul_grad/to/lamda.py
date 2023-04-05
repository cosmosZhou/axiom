from util import *


@apply
def apply(self, i=None):
    expr, *limits_d = self.of(Derivative @ OneMatrix)
    (x, S[1]), = limits_d
    if i is None:
        i = self.generate_var(integer=True)
    expr = expr._subs(x, x[i])
    [n] = self.shape

    return Equal(self, Lamda[i:n](Derivative[x[i]](expr)))


@prove
def prove(Eq):
    from axiom import calculus, algebra, discrete

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Derivative[x](f(x)) @ OneMatrix(n))

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.mul.lamda)

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul_lamda.to.lamda)



    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)




if __name__ == '__main__':
    run()
# created on 2023-03-19
