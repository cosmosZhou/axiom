from util import *


@apply
def apply(self):
    (expr, *limits_d), *limits_e = self.of(Expectation[Derivative])    
    variables = [v for v, _ in limits_d]
    for limit in limits_e:
        assert not limit.has(*variables)
    
    return Equal(self, Derivative(Expectation(expr, *limits_e), *limits_d))


@prove
def prove(Eq):
    from axiom import stats, calculus

    D, n = Symbol(integer=True, positive=True)
    # D denotes the size of the trainable weights
    x = Symbol(real=True, shape=(n,), random=True)
    θ = Symbol(real=True, shape=(D,))
    f = Function(real=True)
    Eq << apply(Expectation[x](Derivative[θ](f[θ](x))))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.integral)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.integral)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-04
# updated on 2023-04-12
