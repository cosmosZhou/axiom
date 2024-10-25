from util import *


@apply
def apply(self):
    (y, x), S[y] = self.of(Equal[Conditioned])
    x, S[x.var] = x.of(Equal)
    assert y.is_random and x.is_random
    return Equal(Expectation(x * y), Expectation(x) * Expectation(y))


@prove
def prove(Eq):
    from axiom import stats, calculus

    y, x = Symbol(real=True, random=True) # rewards
    Eq << apply(Equal(y | x, y))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << stats.eq_conditioned.then.eq.mul.prob.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.mul)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.expect)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.expect)

    # https://danieltakeshi.github.io/2017/03/28/going-deeper-into-reinforcement-learning-fundamentals-of-policy-gradients/ (Approximation (ii))


if __name__ == '__main__':
    run()
# created on 2023-04-09
