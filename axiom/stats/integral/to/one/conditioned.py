from util import *


@apply
def apply(self):
    from axiom.stats.sum.to.one.conditioned import extract
    return Equal(self, extract(Integral, self))


@prove
def prove(Eq):
    from axiom import stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Probability(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(stats.prob.to.mul.bayes)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.prob)

    
    


if __name__ == '__main__':
    run()
# created on 2021-07-20
# updated on 2023-03-25
