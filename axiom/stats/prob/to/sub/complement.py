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
    from axiom import stats, algebra, calculus

    x = Symbol(real=True, random=True)
    Eq << apply(Probability(x >= 0))

    Eq << Eq[0].this.lhs.apply(stats.prob.to.integral)

    Eq << Eq[-1].this.rhs.find(Probability).apply(stats.prob.to.integral)

    Eq << algebra.eq.of.eq.transport.apply(Eq[-1], rhs=1)

    Eq << Eq[-1].this.lhs.apply(calculus.add.to.integral.concat)

    Eq << Eq[-1].this.lhs.apply(stats.integral.to.one)


if __name__ == '__main__':
    run()
# created on 2023-04-19
