from util import *


@apply
def apply(self):
    from Axiom.Stats.Sum.eq.One.Conditioned import extract
    return Equal(self, extract(Integral, self))


@prove
def prove(Eq):
    from Axiom import Stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Probability(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(Stats.Prob.eq.Div.Prob.bayes)

    Eq << Eq[-1].this.find(Integral).apply(Stats.Integral.eq.Prob.marginal)





if __name__ == '__main__':
    run()
# created on 2021-07-20
# updated on 2023-03-25
