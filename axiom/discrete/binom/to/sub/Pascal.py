from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, binomial(n + 1, k + 1) - binomial(n, k + 1))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    Eq << apply(Binomial(n, k))

    Eq << Eq[0].this.rhs.find(Binomial).apply(discrete.binom.to.add.Pascal)


if __name__ == '__main__':
    run()
# created on 2023-06-03
