from util import *


@apply
def apply(self):
    S[S.Half], n = self.of(Binomial)
    assert n.is_integer
    assert n >= 0
    return Equal(self, -(-S.One / 4) ** n * Binomial(2 * n, n) / (2 * n - 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, nonnegative=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Binomial(S.One / 2, n))

    Eq << Eq[0].lhs.this.apply(discrete.binom.to.mul.fallingFactorial)

    Eq << Eq[-1].this.find(FallingFactorial).apply(discrete.fallingFactorial.to.prod)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.neg)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.scale, 2)

    Eq << Eq[-1].this.find(Mul).args[:2].apply(algebra.mul.to.pow.mul.base)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.push)

    Eq << Eq[-1].this.find(Product).apply(algebra.prod.to.mul.shift)

    Eq << Eq[0].this.rhs.find(Binomial).apply(discrete.binom.to.div.factorial2)

    Eq << Eq[-1].this.find(Factorial2).apply(discrete.factorial2.to.prod.odd)





if __name__ == '__main__':
    run()

# created on 2020-10-21
# updated on 2023-06-03
