from util import *


def extract(Sum, self):
    args, (x_var, *_) = self.of(Sum[Probability[Conditioned]])
    if args[-1].is_Tuple:
        args, *weights = args

    cond, given = args
    x, S[x_var] = cond.of(Equal)
    return 1

@apply
def apply(self):
    return Equal(self, extract(Sum, self))


@prove
def prove(Eq):
    from Axiom import Stats

    x, y = Symbol(integer=True, random=True)
    Eq << apply(Sum[x.var](Probability(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(Stats.Prob.eq.Div.Prob.bayes)

    Eq << Eq[-1].this.find(Sum).apply(Stats.Sum.eq.Prob)





if __name__ == '__main__':
    run()
# created on 2021-07-18
# updated on 2023-03-25
