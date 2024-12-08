from util import *



@apply
def apply(self):
    from Axiom.Stats.Sum.eq.Prob import marginalize
    return Equal(self, marginalize(Integral, self))


@prove(provable=False)
def prove(Eq):
    from Axiom import Stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Probability(x, y, z)))

    # the following will result in a recursive reasoning:
    # Eq << Eq[-1].this.rhs.apply(Stats.Probability.to.Integral.joint, x)




if __name__ == '__main__':
    run()
# created on 2020-12-07
# updated on 2023-03-27
