from util import *


@apply
def apply(self):
    cond = self.of(Probability)
    if cond.is_Conditioned:
        cond, given = cond.args
    else :
        given = None

    return Equal(self, 1 - Probability(cond.invert(), given=given))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra, Calculus

    x = Symbol(real=True, random=True)
    Eq << apply(Probability(x >= 0))

    Eq << Eq[0].this.lhs.apply(Stats.Prob.eq.Integral)

    Eq << Eq[-1].this.rhs.find(Probability).apply(Stats.Prob.eq.Integral)

    Eq << Algebra.Eq.of.Eq.transport.apply(Eq[-1], rhs=1)

    Eq << Eq[-1].this.lhs.apply(Calculus.Add.eq.Integral.concat)

    Eq << Eq[-1].this.lhs.apply(Stats.Integral.eq.One)


if __name__ == '__main__':
    run()
# created on 2023-04-19
