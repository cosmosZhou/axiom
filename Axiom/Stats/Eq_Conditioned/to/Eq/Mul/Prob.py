from util import *


@apply
def apply(given):
    (x, y), S[x] = given.of(Equal[Conditioned])

    return Equal(Probability(x, y), Probability(x) * Probability(y))


@prove
def prove(Eq):
    from Axiom import Stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(x | y, x))

    Eq << Stats.Eq.to.Eq.Prob.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.lhs.apply(Stats.Prob.eq.Div.Prob.bayes)



    Eq << Eq[-1] * Probability(y)




if __name__ == '__main__':
    run()
# created on 2020-12-14

# updated on 2023-04-19
