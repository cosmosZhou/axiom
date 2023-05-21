from util import *


@apply
def apply(dist, n=None):
    x, i = dist.of(Distributed[Indexed, NormalDistribution[Zero, One]])
    return Distributed(Sum[i:n](x[i] ** 2), ChiSquaredDistribution(n))


@prove
def prove(Eq):
    from axiom import stats

    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), random=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Distributed(x[i], NormalDistribution(0, 1)), n)

    y = Symbol(real=True)
    Eq << stats.distributed.given.eq.prob.apply(Eq[-1], y)
    

    return
    Eq << stats.imply.eq.chiSquared.induct.apply(Symbol('Y', Lamda[k](Sum[i:k](X[i] * X[i]))), Y)
    Eq << Eq[-1].this.lhs.args[0].args[0].definition
    #https://www.asmeurer.com/blog/
    
    


if __name__ == '__main__':
    run()
# created on 2021-07-18
# updated on 2023-04-30
