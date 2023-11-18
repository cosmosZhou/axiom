from util import *


@apply
def apply(self):
    ((k, n), (S[n], S[k]), S[(-1) ** k]), (S[k], S[0], S[n + 1]) = self.of(Sum[Symbol ** Expr * binomial * Expr])
    return Equal(self, factorial(n) * (-1) ** n)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n + 1]((-1) ** k * k ** n * binomial(n, k)))

    Eq << Eq[-1].this.find(Factorial).apply(discrete.factorial.to.sum.binom)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul)


if __name__ == '__main__':
    run()
# created on 2023-06-17
