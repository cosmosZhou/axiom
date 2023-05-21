from util import *


@apply
def apply(self, order=None):
    from axiom.stats.KL.to.sum import extract
    return Equal(self, extract(Integral, self, order))


@prove
def prove(Eq):
    from axiom import stats
    
    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    Eq << apply(KL(Probability[θ](Equal(x, x.var)), Probability[θ_quote](Equal(x, x.var))))
    
    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.expect)
    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.integral)


if __name__ == '__main__':
    run()
# created on 2023-03-25
