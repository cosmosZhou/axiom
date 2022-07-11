from util import *


@apply
def apply(self, d):
    n = self.of(Binomial[Expr, 2])
    assert d >= 0 and d <= n
    return Equal(self, binomial(n - d, 2) + binomial(d, 2) + (n - d) * d)


@prove
def prove(Eq):
    from axiom import discrete

    x, y = Symbol(integer=True, nonnegative=True)
    Eq << apply(Binomial(x + y, 2), x)

    Eq << Eq[-1].this.lhs.apply(discrete.binom.to.mul.fallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial)

    Eq << Eq[-1].this.lhs.expand()
    Eq << Eq[-1].this.rhs.expand()


if __name__ == '__main__':
    run()
# created on 2022-07-11
