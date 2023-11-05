from util import *


@apply
def apply(ne_zero, dist, b=0):
    a = ne_zero.of(Unequal[0])
    x, (mu, sigma) = dist.of(Distributed[Symbol, NormalDistribution])
    return Distributed(a * x + b, NormalDistribution(a * mu + b, a ** 2 * sigma))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x = Symbol(real=True, random=True)
    mu, b = Symbol(real=True)
    sigma = Symbol(positive=True)
    a = Symbol(real=True)
    Eq << apply(Unequal(a, 0), Distributed(x, NormalDistribution(mu, sigma ** 2)), b)

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=a > 0)

    Eq << algebra.infer.given.et.infer.invert.apply(Eq[-1], cond=a < 0)

    Eq <<= algebra.cond.infer.given.et.infer.et.apply(Eq[1], Eq[-3]), algebra.cond.infer.given.et.infer.et.apply(Eq[1], Eq[-1])

    Eq << Eq[-2].this.lhs.apply(stats.gt_zero.distributed.imply.distributed.scale.gaussian, b)

    Eq << Eq[-1].this.lhs.apply(stats.lt_zero.distributed.imply.distributed.scale.gaussian, b)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-11
# updated on 2023-10-03
