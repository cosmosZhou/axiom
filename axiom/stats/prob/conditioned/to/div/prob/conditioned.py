from util import *


@apply
def apply(self, pivot=-1):
    y, given = self.of(Probability[Conditioned[And]])
    x, z = std.array_split(given, pivot)
    x = And(*x)
    z = And(*z)
    return Equal(self, Probability(x & y, given=z) / Probability(x, given=z))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Probability(y | x & z))

    Eq << algebra.cond.given.infer.domain_defined.apply(Eq[0])

    Eq << algebra.infer_et.given.infer_et.et.apply(Eq[-1], -1)

    Eq << Eq[-1].this.rhs.apply(algebra.ne_zero.eq.given.et.mul)

    Eq << Eq[-1].this.lhs.args[1].apply(stats.ne_zero.imply.eq.prob.conditioned.to.mul.prob.conditioned.bayes, x, y)

    Eq << Eq[-1].this.rhs.reversed





if __name__ == '__main__':
    run()
# created on 2023-10-13
# updated on 2023-10-14
