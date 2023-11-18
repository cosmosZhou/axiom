from util import *


@apply
def apply(self):
    from axiom.stats.expect.sum.to.sum.expect import extract
    return Equal(self, extract(Lamda, self))



@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Expectation(Lamda[k:n](f(x[k])) | s))

    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.integral)

    Eq << Eq[-1].this.lhs.find(Mul).apply(algebra.mul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.lamda)

    Eq << Eq[-1].this.expr.rhs.find(Probability).apply(stats.prob.to.integral.joint, x[k + 1:n])

    Eq << Eq[-1].this.find(And).apply(algebra.eq.eq.to.eq.concat)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.concat)

    Eq << Eq[-1].this.rhs.find(Probability).apply(stats.prob.to.integral.joint, x[:k])

    Eq << Eq[-1].this.find(And).apply(algebra.eq.eq.to.eq.concat)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.concat)


if __name__ == '__main__':
    run()
# created on 2023-04-02
