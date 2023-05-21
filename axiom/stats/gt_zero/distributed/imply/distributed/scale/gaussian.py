from util import *


@apply
def apply(gt_zero, dist, b=0):
    a = gt_zero.of(Expr > 0)
    x, (mu, sigma) = dist.of(Distributed[Symbol, NormalDistribution])
    return Distributed(a * x + b, NormalDistribution(a * mu + b, a ** 2 * sigma))


@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    x = Symbol(real=True, random=True)
    mu, b = Symbol(real=True)
    sigma = Symbol(positive=True)
    a = Symbol(real=True)
    Eq << apply(a > 0, Distributed(x, NormalDistribution(mu, sigma ** 2)), b)

    y = Symbol(real=True)
    Eq << stats.distributed.given.eq.prob.apply(Eq[-1], y)

    Eq << algebra.gt_zero.imply.eq.abs.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq.eq_prob, *Eq[-2:] = algebra.et.given.et.apply(Eq[-1], None)

    Eq << algebra.gt_zero.imply.ne_zero.apply(Eq[0])

    Eq << algebra.ne_zero.imply.ne_zero.abs.apply(Eq[-2])

    Eq << Eq.eq_prob.lhs.this.apply(stats.prob.to.grad)

    Eq << stats.distributed.imply.eq.prob.apply(Eq[1])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.mul)

    Eq << algebra.gt_zero.imply.iff.apply(Eq[0], cond=Eq[-1].find(LessEqual))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.doit.bool)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad_integral.to.mul.grad)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp[~Mul]).find(Add).apply(algebra.add.to.mul.together)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-10
# updated on 2023-04-30
