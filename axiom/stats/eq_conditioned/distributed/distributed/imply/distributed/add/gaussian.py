from util import *


@apply
def apply(eq_conditioned, dist0, dist1):
    x0, (mu0, sigma0) = dist0.of(Distributed[Symbol, NormalDistribution])
    x1, (mu1, sigma1) = dist1.of(Distributed[Symbol, NormalDistribution])
    (S[x1], S[x0.as_boolean()]), S[x1] = eq_conditioned.of(Equal[Conditioned])
    return Distributed(x0 + x1, NormalDistribution(mu0 + mu1, sigma0 + sigma1))


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    x0, x1 = Symbol(real=True, random=True)
    mu0, mu1 = Symbol(real=True)
    sigma0, sigma1 = Symbol(positive=True)
    Eq << apply(Equal(x1 | x0, x1), Distributed(x0, NormalDistribution(mu0, sigma0 ** 2)), Distributed(x1, NormalDistribution(mu1, sigma1 ** 2)))

    y = Symbol(real=True)
    Eq << stats.distributed.given.eq.prob.apply(Eq[-1], y)

    Eq << Eq[-1].lhs.this.apply(stats.prob.to.grad)

    Eq << stats.eq_conditioned.imply.eq.mul.prob.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)


    Eq << stats.distributed.imply.eq.prob.apply(Eq[1])
    Eq << stats.distributed.imply.eq.prob.apply(Eq[2])

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(Exp * ~Integral).apply(calculus.integral.to.mul)

    Eq << Eq[-1].this.find(Integral, Integral).apply(calculus.integral.doit.bool)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.integral)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad_integral.to.mul.grad)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp * Exp).apply(algebra.mul.to.exp)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral_exp.to.mul.quadratic)

    Eq << Eq[-1].this.find(Exp[Mul[~Add]]).apply(algebra.poly.square_completing, y)





if __name__ == '__main__':
    run()

# created on 2021-07-25
# updated on 2023-04-30
