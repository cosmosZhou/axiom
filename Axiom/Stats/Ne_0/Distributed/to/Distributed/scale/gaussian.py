from util import *


@apply
def apply(ne_zero, dist, b=0):
    a = ne_zero.of(Unequal[0])
    x, (mu, sigma) = dist.of(Distributed[Symbol, NormalDistribution])
    return Distributed(a * x + b, NormalDistribution(a * mu + b, a ** 2 * sigma))


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    x = Symbol(real=True, random=True)
    mu, b = Symbol(real=True)
    sigma = Symbol(positive=True)
    a = Symbol(real=True)
    Eq << apply(Unequal(a, 0), Distributed(x, NormalDistribution(mu, sigma ** 2)), b)

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=a > 0)

    Eq << Algebra.Imply.of.And.Imply.invert.apply(Eq[-1], cond=a < 0)

    Eq <<= Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[1], Eq[-3]), Algebra.Cond.Imply.of.And.Imply.And.apply(Eq[1], Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Stats.Gt_0.Distributed.to.Distributed.scale.gaussian, b)

    Eq << Eq[-1].this.lhs.apply(Stats.Lt_0.Distributed.to.Distributed.scale.gaussian, b)





if __name__ == '__main__':
    run()
# created on 2023-04-11
# updated on 2023-10-03
