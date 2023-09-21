from util import *


@apply
def apply(self):
    (ik, i), (k, S[0], n) = self.of(Sum[Binomial])
    S[k] = ik - i
    return Equal(self, Binomial(n + i, i + 1))


@prove
def prove(Eq):
    from axiom import discrete, algebra

    n = Symbol(integer=True, positive=True)
    k, i = Symbol(integer=True)
    Eq << apply(Sum[k:n](Binomial(i + k, i)))

    Eq << Eq[-1].this.lhs.expr.apply(discrete.binom.to.sub.Pascal)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.telescope)


if __name__ == '__main__':
    run()
# created on 2023-06-03
