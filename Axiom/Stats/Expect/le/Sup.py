from util import *


@apply
def apply(self):
    from Axiom.Stats.Expect.ge.Inf import extract
    return LessEqual(self, Sup(*extract(self)), evaluate=False)


@prove
def prove(Eq):
    from Axiom import Stats, Algebra, Calculus

    D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    f = Function(real=True)
    Eq << apply(Expectation[θ](f(x)))

    Eq << Eq[-1].this.lhs.apply(Stats.Expect.eq.Integral)

    Eq << Algebra.All_Le_Sup.apply(Eq[1].rhs)

    Eq << Stats.Prob.ge.Zero.apply(Eq[-2].find(Probability))

    Eq << Algebra.Ge_0.Le.to.Le.Mul.apply(Eq[-1], Eq[-2])

    Eq << Calculus.Le.to.Le.Integral.apply(Eq[-1], [x.var])

    Eq << Eq[-1].this.find(Integral[Probability]).apply(Stats.Integral.eq.One)





if __name__ == '__main__':
    run()
# created on 2023-04-04
# updated on 2023-04-22