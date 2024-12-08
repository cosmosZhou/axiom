from util import *


@apply
def apply(self, pivot=-1):
    args, given = self.of(Probability[Conditioned[And]])
    x, y = std.array_split(args, pivot)
    x = And(*x)
    y = And(*y)
    return Equal(self, Probability(y, given=x & given) * Probability(x, given=given))


@prove
def prove(Eq):
    from Axiom import Stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Probability(y & x | z))


    Eq << Eq[0].this.rhs.args[1].apply(Stats.Prob.Conditioned.eq.Div.Prob.Conditioned)



if __name__ == '__main__':
    run()
# created on 2023-10-14
