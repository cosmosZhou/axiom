from util import *


@apply
def apply(dist):
    x, (μ, Σ) = dist.of(Distributed[NormalDistribution])
    return Equal(μ, Expectation(x)), Equal(Σ, Variance(x))


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n,), random=True)
    μ = Symbol(shape=(n,), real=True)
    Σ = Symbol(shape=(n, n), real=True)
    Eq << apply(Distributed(x, NormalDistribution(μ, Σ)))

    Eq << stats.distributed.imply.eq.prob.apply(Eq[0])

    Eq << Expectation(x).this.apply(stats.expect.to.integral)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.mul)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.offset, μ)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.add)

    Eq << Eq[-1].this.find(Integral[2]).apply(calculus.integral.to.mul)

    #https://en.wikipedia.org/wiki/Cholesky_decomposition


if __name__ == '__main__':
    run()
# created on 2023-04-30
