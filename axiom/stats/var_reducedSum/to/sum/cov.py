from util import *


@apply
def apply(self, i=None, j=None):
    (x, (S[0], n)), [S[x[:n]]] = self.of(Variance[ReducedSum[Sliced]])
    return Equal(self, Sum[j:n, i:n](Covariance(x[i], x[j])))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x = Symbol(real=True, shape=(oo,), random=True)
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Variance(ReducedSum(x[:n])), i, j)

    Eq << Eq[0].this.find(ReducedSum).apply(algebra.reducedSum.to.sum)

    Eq << Eq[-1].this.lhs.apply(stats.var_sum.to.sum.cov)




if __name__ == '__main__':
    run()
# created on 2023-04-19

