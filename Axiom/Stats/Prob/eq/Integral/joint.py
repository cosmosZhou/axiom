from util import *


@apply
def apply(self, y):
    from Axiom.Stats.Prob.eq.Sum.joint import rewrite
    return Equal(self, rewrite(Integral, self, y))


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Probability(x), y)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Equal(Probability(x), 0))

    Eq << Eq[-1].this.lhs.apply(Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes, y)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(Integral).simplify()

    Eq << Eq[-1].this.find(Integral).apply(Stats.Integral.eq.One.Conditioned)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(Stats.Eq_0.to.Eq_0.joint, y)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-21
# updated on 2023-03-30
