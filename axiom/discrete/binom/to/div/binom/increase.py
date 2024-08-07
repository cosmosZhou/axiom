from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, Binomial(n + 1, k) / (n + 1) * (n + 1 - k))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n))
    Eq << apply(Binomial(n, k))

    Eq << Eq[-1].this.rhs.find(binomial).apply(discrete.binom.to.div.binom.decrease)

    

    

    

    


if __name__ == '__main__':
    run()
# created on 2023-06-03
