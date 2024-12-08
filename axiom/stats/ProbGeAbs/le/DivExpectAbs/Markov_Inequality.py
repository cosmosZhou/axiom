from util import *


@apply
def apply(x, a):
    assert a >= 0
    return LessEqual(Probability(Abs(x) >= a), Expectation(Abs(x)) / a)


@prove
def prove(Eq):
    from Axiom import Stats, Calculus, Algebra

    x = Symbol(real=True, random=True)
    a = Symbol(positive=True)
    Eq << apply(x, a)

    Eq << Eq[0].find(Expectation).this.apply(Stats.Expect.eq.Integral)

    Eq.eq = Eq[-1].this.rhs.apply(Calculus.Integral.eq.Add.split, 0)

    Eq << Eq.eq.find(Integral).this.apply(Calculus.Integral.eq.Add.split, a)

    Eq << Algebra.Eq.to.Ge.relax.apply(Eq[-1], Eq[-1].find(Integral[2]))

    Eq << Eq[-1].this.rhs.find(Abs).apply(Algebra.Abs.eq.Piece)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.limits.offset, a)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Add)

    Eq << Algebra.Ge.to.Ge.relax.apply(Eq[-1], Eq[-1].rhs.find(Integral))

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Mul)

    Eq << Eq[-1].this.rhs.find(Integral).apply(Calculus.Integral.limits.offset, -a)

    Eq.ge = Eq[-1].this.rhs.find(Integral).apply(Stats.Integral.eq.Prob)

    Eq << Eq.eq.find(Integral[2]).this.apply(Calculus.Integral.eq.Add.split, -a)

    Eq << Algebra.Eq.to.Ge.relax.apply(Eq[-1], Eq[-1].rhs.find(Integral))

    Eq << Eq[-1].this.rhs.find(Abs).apply(Algebra.Abs.eq.Piece)

    Eq << Eq[-1].this.rhs.find(Integral).apply(Calculus.Integral.limits.offset, -a)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(-~Integral).apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.find(Integral[-Expr]).apply(Calculus.Integral.eq.Mul)

    Eq << Algebra.Ge.to.Ge.relax.apply(Eq[-1], Eq[-1].find(Mul[Integral]))

    Eq << Eq[-1].this.find(Mul[~Integral]).apply(Calculus.Integral.limits.offset, a)

    Eq << Eq[-1].this.rhs.find(Integral).apply(Stats.Integral.eq.Prob)

    Eq << Eq[-1] + Eq.ge

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Mul)

    Eq << Algebra.Eq.Ge.to.Ge.subs.apply(Eq.eq, Eq[-1])

    Eq << Eq[-1] / a

    Eq << Eq[-1].reversed

    Eq << Eq[0].lhs.this.find(GreaterEqual).apply(Algebra.GeAbs.equ.Or)

    Eq << Eq[-1].this.rhs.apply(Stats.Prob.Or.eq.Add)

    Eq << Eq[-3].subs(Eq[-1].reversed)





if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-05-20
