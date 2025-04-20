from util import *


@apply
def apply(self):
    from Axiom.Probability.Expect.Sum.eq.Sum.Expect import extract
    return Equal(self, extract(Lamda, self))



@prove
def prove(Eq):
    from Axiom import Probability, Algebra, Calculus

    n = Symbol(integer=True, positive=True)
    f = Function(real=True)
    s = Symbol(integer=True, random=True)
    x = Symbol(real=True, random=True, shape=(oo,))
    k = Symbol(integer=True)
    Eq << apply(Expectation(Lamda[k:n](f(x[k])) | s))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.lhs.find(Mul).apply(Algebra.Mul.eq.Lamda)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.eq.Lamda)

    Eq << Eq[-1].this.expr.rhs.find(Pr).apply(Probability.Pr.eq.Integral.joint, x[k + 1:n])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.Is.Eq.concat)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.limits.concat)

    Eq << Eq[-1].this.rhs.find(Pr).apply(Probability.Pr.eq.Integral.joint, x[:k])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.Is.Eq.concat)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.limits.concat)


if __name__ == '__main__':
    run()
# created on 2023-04-02
