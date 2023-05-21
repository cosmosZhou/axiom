from util import *


@apply
def apply(self, *vars):
    given = S.true
    for v in vars:
        given &= Equal(v, v.surrogate)
        assert v.is_probable
    
    lhs, rhs = self.of(Covariance)
    assert not lhs.is_Conditioned
    assert not rhs.is_Conditioned

    return Equal(self, 
                 Covariance(Expectation(lhs | given), Expectation(rhs | given)) + Expectation(Covariance(lhs, rhs, given=given)))

@prove
def prove(Eq):
    from axiom import stats

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, random=True, shape=(n,))
    z = Symbol(real=True, probable=True)
    Eq << apply(Covariance(x, y), z)

    Eq << Eq[0].this.rhs.find(Covariance).apply(stats.cov_expect.to.sub.expect)

    Eq << Eq[-1].this.find(Expectation[Covariance]).apply(stats.expect_cov.to.sub.expect)

    Eq << Eq[-1].this.lhs.apply(stats.cov.to.sub.expect)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
