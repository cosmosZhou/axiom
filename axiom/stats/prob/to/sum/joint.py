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
    from axiom import algebra, stats

    x, y = Symbol(integer=True, random=True)
    Eq << apply(Probability(x), y)

    Eq << algebra.cond.of.et.infer.split.apply(Eq[0], cond=Equal(Probability(x), 0))

    Eq << Eq[-1].this.lhs.apply(stats.ne_zero.then.eq.prob.to.mul.prob.bayes, y)

    Eq << algebra.infer.of.infer.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(Sum).simplify()

    Eq << Eq[-1].this.find(Sum).apply(stats.sum.to.one.conditioned)

    Eq << algebra.infer.of.infer.subs.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(stats.is_zero.then.is_zero.joint, y)

    Eq << algebra.infer.of.infer.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-30
