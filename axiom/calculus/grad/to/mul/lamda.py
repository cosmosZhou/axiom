from util import *


@apply
def apply(self, i=None):
    expr, *limits_d = self.of(Derivative)
    (x, S[1]), = limits_d
    if i is None:
        i = Symbol(integer=True)
    expr = expr._subs(x, x[i])
    n, = x.shape
    return Equal(self, Identity(n) * Lamda[i:n](Derivative[x[i]](expr)))


@prove
def prove(Eq):
    from axiom import algebra, calculus

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    x = Symbol(real=True, shape=(n,))
    Eq << apply(Derivative[x](f(x)))

    j = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], j)

    i = Symbol(domain=Range(n))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], i)

    Eq << Eq[-1].this.lhs.apply(calculus.grad.to.mul.grad)












if __name__ == '__main__':
    run()
# created on 2023-03-18
