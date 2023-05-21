from util import *


@apply
def apply(self, j=None):
    (xi, (i, S[0], n)), *limits_v = self.of(Variance[Sum])
    assert not self.is_random
    assert i != j
    if j is None:
        j = self.generate_var(integer=True, excludes=i)
    xj = xi._subs(i, j)
    assert not xj._has(i)
    return Equal(self, Sum[i:n](Variance(xi)) + Sum[j:i, i:n](Covariance(xi, xj) + Covariance(xj, xi)))


@prove
def prove(Eq):
    from axiom import stats, algebra

    x = Symbol(real=True, shape=(oo,), random=True)
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Variance(Sum[i:n](x[i])), j)

    Eq << Eq[0].this.lhs.apply(stats.var_sum.to.sum.cov)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add.split.limits)

    Eq << Eq[-1].this.find(Covariance).apply(stats.cov.to.var)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-19

# updated on 2023-05-02
