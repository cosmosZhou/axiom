from util import *


@apply
def apply(self, k=None): 
    (s, (S[0], n)), S[s[:n].var] = self.of(Probability[Equal[Sliced]])
    return Equal(self, Product[k:n](Probability(s[k] | s[:k])), evaluate=False)


@prove
def prove(Eq):
    from axiom import stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, nonnegative=True)  # total time step
    Eq << apply(Probability(s[:n]), k)

    Eq << Eq[0].this.rhs.apply(stats.prod.to.prob.joint)

    #https://arxiv.org/pdf/1909.08593.pdf
    #We begin with a vocabulary Σ and a language model ρ which defines a probability distribution over sequences of tokens


if __name__ == '__main__':
    run()
# created on 2023-04-08
