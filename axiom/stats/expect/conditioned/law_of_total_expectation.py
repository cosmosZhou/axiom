from util import *


@apply
def apply(self):
    from axiom.stats.expect.law_of_total_expectation import rewrite
    return Equal(self, rewrite(self))
    

@prove
def prove(Eq):
    from axiom import stats, calculus

    x, y, z = Symbol(real=True, random=True)
    f = Function(real=True)
    Eq << apply(Expectation(Expectation(f(x, y, z) | y.surrogate & z) | z))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.lhs.find(Expectation).apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.div.prob.bayes)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.div.prob.bayes)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.div.prob.bayes)

    


if __name__ == '__main__':
    run()
# created on 2023-04-22
