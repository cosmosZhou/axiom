from util import *


@apply
def apply(self):
    expr, *limits = self.of(Expectation)
    vars = []
    for x, *ab in self.limits:
        assert not ab
        vars.append((x.var,))
        expr = expr._subs(x, x.var)
    return GreaterEqual(self, Inf(expr, *vars), evaluate=False)


@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << algebra.imply.all.ge_inf.apply(Eq[1].rhs)

    Eq << stats.imply.ge_zero.prob.apply(Eq[-2].find(Probability))

    Eq << algebra.ge_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[-2])

    Eq << calculus.ge.imply.ge.integral.apply(Eq[-1], [x.var])

    Eq << Eq[-1].this.find(Integral[Probability]).apply(stats.integral.to.one)

    


if __name__ == '__main__':
    run()
# created on 2023-04-04
