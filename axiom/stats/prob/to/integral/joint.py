from util import *


@apply
def apply(self, y):
    from axiom.stats.prob.to.sum.joint import rewrite
    return Equal(self, rewrite(Integral, self, y))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x, y = Symbol(real=True, random=True)
    Eq << apply(Probability(x), y)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[0], cond=Equal(Probability(x), 0))

    Eq << Eq[-1].this.lhs.apply(stats.ne_zero.imply.eq.prob.to.mul.prob.bayes, y)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << Eq[-1].this.find(Integral).simplify()

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.one.conditioned)

    Eq << algebra.infer.given.infer.subs.apply(Eq[1])

    Eq << Eq[-1].this.rhs.reversed

    Eq << Eq[-1].this.lhs.apply(stats.is_zero.imply.is_zero.joint, y)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-21
# updated on 2023-03-30
