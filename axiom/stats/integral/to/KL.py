from util import *


@apply
def apply(self, order=None):
    from axiom.stats.sum.to.KL import extract
    return Equal(self, extract(Integral, self, order))


@prove
def prove(Eq):
    from axiom import stats
    
    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    Eq << apply(Integral[x.var](log(Probability[θ](x) / Probability[θ_quote](x)) * Probability[θ](x)))
    
    Eq << Eq[-1].this.rhs.apply(stats.KL.to.integral)


if __name__ == '__main__':
    run()
# created on 2023-03-26
