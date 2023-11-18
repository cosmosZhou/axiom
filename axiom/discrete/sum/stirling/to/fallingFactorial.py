from util import *


@apply
def apply(self):
    ((x, k), (n, S[k]), exp), (k, S[0], S[n + 1]) = self.of(Sum[Pow * Stirling1 * (-1) ** Expr])
    assert exp in (n + k, n - k)
    return Equal(self, FallingFactorial(x, n))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](x ** k * Stirling1(n, k) * (-1) ** (n - k)))

    Eq << discrete.risingFactorial.to.sum.stirling.apply(RisingFactorial(-x, n), k)

    Eq << Eq[-1].this.lhs.apply(discrete.risingFactorial.to.mul.fallingFactorial)

    Eq << Eq[-1].this.rhs.find(Pow).apply(algebra.pow.to.mul.split.base)

    Eq << Eq[-1] * (-1) ** n

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].reversed

    


if __name__ == '__main__':
    run()
# created on 2023-08-26
