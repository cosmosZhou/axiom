from util import *


@apply
def apply(self):
    x, y = self.of(Covariance)
    assert not x.is_Conditioned
    assert not y.is_Conditioned

    return Equal(self, Covariance(x, Expectation(y | x.surrogate)))

@prove
def prove(Eq):
    from axiom import stats

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, random=True, shape=(n,))
    Eq << apply(Covariance(x, y))

    Eq << Eq[0].this.lhs.apply(stats.cov.to.sub.expect)

    Eq << Eq[-1].this.rhs.apply(stats.cov.to.sub.expect)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(stats.expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Mul[Expectation]).apply(stats.mul.to.expect)

    Eq << Eq[-1].this.rhs.apply(stats.expect.law_of_total_expectation)

    


if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
