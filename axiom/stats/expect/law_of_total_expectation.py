from util import *


@apply
def apply(self):
    ((expr, given), *limits_inner), *limits = self.of(Expectation[Expectation[Conditioned]])
    if given.is_Equal:
        x, S[x.surrogate] = given.args
    else:
        vars = set()
        for cond in given.of(And):
            x, S[x.surrogate] = cond.of(Equal)
            vars.add(x)
            
        for x, *cond in limits:
            assert not cond
            assert x in vars
      
    rhs = Expectation(expr, *limits_inner)
    assert rhs.random_symbols == self.random_symbols
    return Equal(self, rhs)


@prove
def prove(Eq):
    from axiom import stats, calculus

    x, y = Symbol(real=True, random=True)
    f = Function(real=True)
    Eq << apply(Expectation(Expectation(f(x) | y.surrogate)))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.lhs.find(Expectation).apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Probability[Conditioned]).apply(stats.prob.to.mul.bayes)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Mul[~Integral]).apply(stats.integral.to.prob)
    

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)


if __name__ == '__main__':
    run()
# created on 2023-03-31
