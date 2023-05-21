from util import *


@apply
def apply(x, a):
    assert a >= 0
    return LessEqual(Probability(Abs(x) >= a), Expectation(Abs(x)) / a)


@prove
def prove(Eq):
    from axiom import stats, calculus, algebra

    x = Symbol(real=True, random=True)
    a = Symbol(positive=True)
    Eq << apply(x, a)

    Eq << Eq[0].find(Expectation).this.apply(stats.expect.to.integral)

    Eq.eq = Eq[-1].this.rhs.apply(calculus.integral.to.add.concat, 0)

    Eq << Eq.eq.find(Integral).this.apply(calculus.integral.to.add.concat, a)

    Eq << algebra.eq.imply.ge.relax.apply(Eq[-1], Eq[-1].find(Integral[2]))

    Eq << Eq[-1].this.rhs.find(Abs).apply(algebra.abs.to.piece)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.offset, a)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.add)

    Eq << algebra.ge.imply.ge.relax.apply(Eq[-1], Eq[-1].rhs.find(Integral))

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.mul)

    Eq << Eq[-1].this.rhs.find(Integral).apply(calculus.integral.limits.offset, -a)

    Eq.ge = Eq[-1].this.rhs.find(Integral).apply(stats.integral.to.prob)

    Eq << Eq.eq.find(Integral[2]).this.apply(calculus.integral.to.add.concat, -a)

    Eq << algebra.eq.imply.ge.relax.apply(Eq[-1], Eq[-1].rhs.find(Integral))

    Eq << Eq[-1].this.rhs.find(Abs).apply(algebra.abs.to.piece)

    Eq << Eq[-1].this.rhs.find(Integral).apply(calculus.integral.limits.offset, -a)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(-~Integral).apply(calculus.integral.to.add)

    Eq << Eq[-1].this.find(Integral[-Expr]).apply(calculus.integral.to.mul)

    Eq << algebra.ge.imply.ge.relax.apply(Eq[-1], Eq[-1].find(Mul[Integral]))

    Eq << Eq[-1].this.find(Mul[~Integral]).apply(calculus.integral.limits.offset, a)

    Eq << Eq[-1].this.rhs.find(Integral).apply(stats.integral.to.prob)

    Eq << Eq[-1] + Eq.ge

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.mul)

    Eq << algebra.eq.ge.imply.ge.subs.apply(Eq.eq, Eq[-1])

    Eq << Eq[-1] / a

    Eq << Eq[-1].reversed

    Eq << Eq[0].lhs.this.find(GreaterEqual).apply(algebra.abs_ge.to.ou)

    Eq << Eq[-1].this.rhs.apply(stats.prob_ou.to.add)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-05-20
