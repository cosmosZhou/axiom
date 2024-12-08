from util import *


@apply
def apply(self):
    x, S[x] = self.of(Covariance)
    return Equal(self, Variance(x))

@prove
def prove(Eq):
    from Axiom import Stats

    n = Symbol(integer=True, positive=True)
    x = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Covariance(x, x))

    Eq << Eq[0].this.rhs.apply(Stats.Var.eq.Cov)


if __name__ == '__main__':
    run()
# created on 2023-04-19
