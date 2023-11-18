from util import *


@apply
def apply(dist):
    x = dist.of(Distributed[NormalDistribution[Zero, One]])
    return Distributed(x ** 2, ChiSquaredDistribution(1))


@prove
def prove(Eq):
    from axiom import stats, calculus, sets

    x = Symbol(real=True, random=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Distributed(x, NormalDistribution(0, 1)))

    Eq << stats.distributed.imply.eq.prob.apply(Eq[0])

    y = Symbol(real=True, nonnegative=True)
    Eq << stats.distributed.given.eq.prob.apply(Eq[1], y)

    Eq << Eq[-1].lhs.this.apply(stats.prob.to.grad)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.add.split, 0)

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(Integral[2]).apply(calculus.integral.limits.subs, x.var, -x.var)

    Eq << Eq[-1].this.find(Mul[~Integral]).apply(calculus.integral.to.neg)

    Eq << Eq[-1].this.find(Integral).simplify()

    Eq << Eq[-1].this.find(LessEqual).apply(sets.square_le.to.el.interval)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.absorb)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.integral.to.mul.grad)

    Eq << Eq[-1].this.find(Derivative).doit()
    #https://www.asmeurer.com/blog/




if __name__ == '__main__':
    run()
# created on 2021-07-18
# updated on 2023-06-18
