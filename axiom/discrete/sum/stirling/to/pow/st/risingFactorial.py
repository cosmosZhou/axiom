from util import *


@apply
def apply(self):
    ((x, k), (n, S[k]), exp), (k, S[0], S[n + 1]) = self.of(Sum[RisingFactorial * Stirling * (-1) ** Expr])
    assert exp in (n + k, n - k)
    return Equal(self, x ** n)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](RisingFactorial(x, k) * Stirling(n, k) * (-1) ** (n - k)))

    Eq << discrete.pow.to.sum.stirling.fallingFactorial.apply((-x) ** n, k)

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.mul.risingFactorial)

    Eq << Eq[-1] * (-1) ** n

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-08-26
