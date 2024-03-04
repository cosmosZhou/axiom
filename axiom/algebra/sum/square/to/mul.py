from util import *


@apply
def apply(self):
    k, (S[k], S[0], n) = self.of(Sum[Expr ** 2])
    return Equal(self, n * (2 * n - 1) * (n - 1) / 6)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(Sum[k:n](k ** 2))

    Eq << Binomial(k, 2).this.apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1] * 2

    Eq << Eq[-1].this.rhs.apply(algebra.mul.to.add)

    Eq << Eq[-1].reversed + k

    Eq << algebra.eq.imply.eq.sum.apply(Eq[-1], (k, 0, n), simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.series.arithmetic)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.subs.offset, 2)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum.binom.to.binom)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[0].this.rhs.args[::3].simplify()

    


if __name__ == '__main__':
    run()
# created on 2023-12-13
