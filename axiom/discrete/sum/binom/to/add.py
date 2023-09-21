from util import *


@apply
def apply(self):
    ((n, k), S[k]), (S[k], i, m) = self.of(Sum[Binomial * (-1) ** Symbol])
    m -= 1
    return Equal(self, Binomial(n - 1, m) * (-1) ** m + Binomial(n - 1, i - 1) * (-1) ** i)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    m, n, i = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:i:m + 1](Binomial(n, k) * (-1) ** k))

    Eq << Eq[0].this.find(Binomial).apply(discrete.binom.to.add.Pascal)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.expr.args[1].apply(algebra.mul.negate)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.telescope)

    Eq << Eq[-1].this.lhs.apply(algebra.mul.negate, 1)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-21
# updated on 2023-08-19
