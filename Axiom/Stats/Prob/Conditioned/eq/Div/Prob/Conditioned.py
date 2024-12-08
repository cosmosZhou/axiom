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
    from Axiom import Algebra, Stats

    x, y, z = Symbol(real=True, random=True)
    Eq << apply(Probability(y | x & z))

    Eq << Algebra.Cond.of.Imply.domain_defined.apply(Eq[0])

    Eq << Algebra.Imply_And.of.Imply_And.And.apply(Eq[-1], -1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ne_0.Eq.of.And.Mul)

    Eq << Eq[-1].this.lhs.args[1].apply(Stats.Ne_0.to.Eq.Prob.Conditioned.eq.Mul.Prob.Conditioned.bayes, x, y)

    Eq << Eq[-1].this.rhs.reversed





if __name__ == '__main__':
    run()
# created on 2023-10-13
# updated on 2023-10-14
