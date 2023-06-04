from util import *


@apply
def apply(self):
    ((n, k), S[k]), (S[k], S[0], m) = self.of(Sum[Binomial * (-1) ** Symbol])
    m -= 1
    return Equal(self, Binomial(n - 1, m) * (-1) ** m)


@prove
def prove(Eq):
    from axiom import discrete, algebra

    m, n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:m + 1](Binomial(n, k) * (-1) ** k))

    Eq << Eq[0].this.find(Binomial).apply(discrete.binom.to.add.Pascal)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.limits.subs.offset, 1)

    Eq << Eq[-1].this.find((-1) ** Add).apply(algebra.pow.to.mul.split.exponent)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-21
# updated on 2023-04-22
