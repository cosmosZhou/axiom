from util import *


@apply
def apply(self):
    k, (S[k], S[0], n) = self.of(Sum[Expr ** 3])
    return Equal(self, Sum[k:n](k) ** 2)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(3, oo))
    Eq << apply(Sum[k:n](k ** 3))

    Eq << discrete.pow.to.sum.stirling.fallingFactorial.apply(k ** 3)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.doit)

    Eq << Binomial(k, 3).this.apply(discrete.binom.to.mul.fallingFactorial.doit).reversed * 6

    Eq << Binomial(k, 2).this.apply(discrete.binom.to.mul.fallingFactorial.doit).reversed * 2

    Eq << Eq[-3].subs(*Eq[-2:])

    Eq << algebra.eq.then.eq.sum.apply(Eq[-1], (k, 0, n), simplify=None)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.mul.series.arithmetic)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Mul[~Sum][2]).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.subs.offset, 2)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.limits.subs.offset, 3)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum.binom.to.binom)

    Eq << Eq[-1].this.rhs.find(Sum).apply(discrete.sum.binom.to.binom)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.find(Binomial).apply(discrete.binom.to.mul.fallingFactorial.doit)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add[Mul]).expand()

    Eq << Eq[-1].this.find(Add[Mul]).apply(algebra.add.to.mul)

    Eq << Eq[0].this.rhs.find(Sum).apply(algebra.sum.to.mul.series.arithmetic)


if __name__ == '__main__':
    run()
# created on 2023-12-13
