from util import *


@apply
def apply(given):
    ((x, x_var), (y, y_var)), ((S[x_var], (S[y_var], (S[y_var], S[x_var]))), (S[0], S[True])) = given.of(Equal[Probability[Equal & Equal], Piecewise[ExprCondPair[Exp[-Symbol], And[0 < Symbol, Symbol < Symbol]]]])
    return Equal(Probability(x > 5, given=y <= 3), 3 / (Exp(5) - Exp(2)))


@prove
def prove(Eq):
    from axiom import stats, calculus

    x, y = Symbol(real=True, random=True)
    Eq << apply(Equal(Probability(x, y), Piecewise((Exp(-x.var), And(0 < y.var, y.var < x.var)), (0, True))))

    Eq << Eq[-1].lhs.this.apply(stats.prob.to.mul.bayes)

    Eq << Eq[-1].rhs.find(Probability).this.apply(stats.prob.to.integral)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.rhs().find(Min).simplify()

    Eq << Eq[-1].this.rhs.doit()

    Eq.plausible = Eq[2].subs(Eq[-1])

    Eq << Eq.plausible.rhs.find(Probability).this.apply(stats.prob.to.integral)

    Eq << Eq[-1].this.rhs.find(Probability).apply(stats.prob.to.integral.joint, x)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.add.concat, 3)

    Eq << Eq[-1].this.find(Integral)().find(Min).simplify()

    Eq << Eq[-1].this.find(Integral[2])().find(Min).simplify()

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.add.concat, 0)

    Eq << Eq[-1].this.find(Integral)().find(Interval).simplify()

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate, simplify=False)

    Eq << Eq[-1].this.find(Integral)().find(Integral).simplify()

    Eq << Eq[-1].this.find(Integral).doit()

    Eq << Eq[-1].this.find(Integral).doit()

    Eq << Eq.plausible.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul).expand()





if __name__ == '__main__':
    run()
# created on 2023-03-20
# updated on 2023-03-22
