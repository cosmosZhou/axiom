from util import *


def rewrite(Sum, self, *sym):
    conds = self.of(Probability)
    vars = []
    if conds.is_Conditioned:
        conds, given = conds.of(Conditioned)
    else:
        given = None

    limits = []
    for s in sym:
        conds &= s
        limits.append((s.var,))

    expr = Probability(conds, given=given)

    for limit in limits:
        if limit[0].is_integer:
            expr = Sum(expr, limit)
        else:
            expr = Integral(expr, limit)
    return expr

@apply
def apply(self, y):
    assert y.is_integer
    return Equal(self, rewrite(Sum, self, y))


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    x, y = Symbol(integer=True, random=True)
    Eq << apply(Probability(x), y)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[0], cond=Equal(Probability(x), 0))

    Eq << Eq[-1].this.lhs.apply(Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes, y)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(Stats.Sum.eq.One.Conditioned)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(Stats.Eq_0.to.Eq_0.joint, y)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-30
