from util import *


def extract(Sum, self, order):
    ((prob_lhs, prob_rhs), S[prob_lhs]), *limits = self.of(Sum[Log[Probability / Probability] * Probability])

    return KL(Probability(*prob_lhs), Probability(*prob_rhs))

@apply
def apply(self, order=None):
    return Equal(self, extract(Sum, self, order))


@prove
def prove(Eq):
    from Axiom import Stats

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(Sum[x.var](log(Probability[θ](x) / Probability[θ_quote](x)) * Probability[θ](x)))

    Eq << Eq[-1].this.rhs.apply(Stats.KL.eq.Sum)



if __name__ == '__main__':
    run()
# created on 2023-03-26
