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
    return Equal(self, Sum[j:n, i:n](Covariance(xi, xj)))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x = Symbol(real=True, shape=(oo,), random=True)
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Variance(Sum[i:n](x[i])), j)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.apply(stats.var_add.to.add.cov)

    Eq << Eq[-1].this.find(Covariance).apply(stats.cov_sum.to.sum.cov)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.lhs.find(Sum[Covariance]).limits_subs(i, j)

    Eq << Eq[-1].this.find(Variance).apply(stats.var.to.cov)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[~Sum]).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Covariance).apply(stats.cov_sum.to.sum.cov)

    Eq << Infer(Eq[0], Eq.induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], n, 0)




if __name__ == '__main__':
    run()
# created on 2023-04-19

