from util import *


@apply
def apply(self, k=None):
    ((s, (S[0], n)), S[s[:n].var]), Z = self.of(Probability[Conditioned[Equal[Sliced]]])
    return Equal(self, Product[k:n](Probability(s[k] | s[:k] & Z)), evaluate=False)


@prove
def prove(Eq):
    from axiom import stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    Z = Symbol(shape=(b,), real=True, random=True) #modality
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, nonnegative=True)  # total time step
    Eq << apply(Probability(s[:n] | Z), k)

    Eq << Eq[0].this.rhs.apply(stats.prod.prob.conditioned.to.prob.conditioned)

    #https://arxiv.org/pdf/2309.16058.pdf#3



if __name__ == '__main__':
    run()
# created on 2023-10-13
