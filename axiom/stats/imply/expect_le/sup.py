from util import *


@apply
def apply(self):
    from axiom.stats.imply.expect_ge.inf import extract
    return LessEqual(self, Sup(*extract(self)), evaluate=False)


@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << algebra.imply.all.le_sup.apply(Eq[1].rhs)

    Eq << stats.imply.ge_zero.prob.apply(Eq[-2].find(Probability))

    Eq << algebra.ge_zero.le.imply.le.mul.apply(Eq[-1], Eq[-2])

    Eq << calculus.le.imply.le.integral.apply(Eq[-1], [x.var])

    Eq << Eq[-1].this.find(Integral[Probability]).apply(stats.integral.to.one)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-04
# updated on 2023-04-22
