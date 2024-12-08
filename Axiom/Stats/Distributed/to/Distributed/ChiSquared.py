from util import *


@apply
def apply(dist):
    x = dist.of(Distributed[NormalDistribution[Zero, One]])
    return Distributed(x ** 2, ChiSquaredDistribution(1))


@prove
def prove(Eq):
    from Axiom import Stats, Calculus, Sets

    x = Symbol(real=True, random=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Distributed(x, NormalDistribution(0, 1)))

    Eq << Stats.Distributed.to.Eq.Prob.apply(Eq[0])

    y = Symbol(real=True, nonnegative=True)
    Eq << Stats.Distributed.of.Eq.Prob.apply(Eq[1], y)

    Eq << Eq[-1].lhs.this.apply(Stats.Prob.eq.Grad)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Add.split, 0)

    Eq << Eq[-1].subs(Eq[2])

    Eq << Eq[-1].this.find(Integral[2]).apply(Calculus.Integral.limits.subs, x.var, -x.var)

    Eq << Eq[-1].this.find(Mul[~Integral]).apply(Calculus.Integral.eq.Neg)

    Eq << Eq[-1].this.find(Integral).simplify()

    Eq << Eq[-1].this.find(LessEqual).apply(Sets.LeSquare.equ.In.Interval)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.absorb)

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Integral.eq.Mul.Grad)

    Eq << Eq[-1].this.find(Derivative).doit()
    # https://www.asmeurer.com/blog/




if __name__ == '__main__':
    run()
# created on 2021-07-18
# updated on 2023-06-18
