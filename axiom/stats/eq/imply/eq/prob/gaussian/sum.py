from util import *


@apply
def apply(given):
    ((x0, x0_var), (x1, x1_var)), ((S[x0], S[x0_var]), (S[x1], S[x1_var])) = given.of(Equal[Probability[Equal & Equal], Probability[Equal] * Probability[Equal]])
    mean0, std0 = pspace(x0).distribution.of(NormalDistribution)
    mean1, std1 = pspace(x1).distribution.of(NormalDistribution)

    y = given.generate_var(distribution=NormalDistribution(mean0 + mean1, sqrt(std0 * std0 + std1 * std1)), var='y')
    return Equal(Probability(Equal(x0 + x1, y.var)), Probability(y).doit())


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    mu0, mu1 = Symbol(real=True)
    sigma0, sigma1 = Symbol(positive=True)
    x0 = Symbol(distribution=NormalDistribution(mu0, sigma0))
    x1 = Symbol(distribution=NormalDistribution(mu1, sigma1))
    Eq << apply(Equal(Probability(x0, x1), Probability(x0) * Probability(x1)))

    Eq << Eq[-1].lhs.this.apply(stats.prob.to.grad)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.rhs.find(Probability).doit()

    Eq << Eq[-1].this.rhs.find(Probability).doit()

    Eq << Eq[-1].this.find(LessEqual).apply(algebra.le.transport)

    Eq << Eq[-1].this.find(Integral, Integral).apply(calculus.integral.doit.bool)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad.to.integral)

    Eq << Eq[-1].this.find(Derivative).apply(calculus.grad_integral.to.mul.grad)

    Eq << Eq[-1].this.find(Derivative).doit()

    Eq << Eq[-1].this.find(Exp * Exp).apply(algebra.mul.to.exp)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.mul.st.exp.quadratic)

    Eq << Eq[1].this.find(Add ** 2).apply(algebra.square.to.add)

    Eq << Eq[-1].this.find(Exp).arg.apply(algebra.mul.distribute)





if __name__ == '__main__':
    run()

# created on 2021-07-25
# updated on 2023-03-20
