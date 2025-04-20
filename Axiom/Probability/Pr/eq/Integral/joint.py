from util import *


@apply
def apply(self, y):
    from Axiom.Probability.Pr.eq.Sum.joint import rewrite
    return Equal(self, rewrite(Integral, self, y))


@prove
def prove(Eq):
    from Axiom import Algebra, Probability, Logic

    x, y = Symbol(real=True, random=True)
    Eq << apply(Pr(x), y)

    Eq << Logic.Cond.given.And.Imp.split.apply(Eq[0], cond=Equal(Pr(x), 0))

    Eq << Eq[-1].this.lhs.apply(Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes, y)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(Integral).simplify()

    Eq << Eq[-1].this.find(Integral).apply(Probability.Integral.eq.One.Conditioned)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(Probability.Eq_0.of.Eq_0.joint, y)

    Eq << Logic.Imp.given.Imp.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-21
# updated on 2023-03-30
