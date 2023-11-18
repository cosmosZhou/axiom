from util import *


@apply
def apply(eq_conditioned, eq_expect, eq_var, ε=None, n=None):
    ((x, k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    (S[x[k]], (S[x[k]],)), μ = eq_expect.of(Equal[Expectation])
    (S[x[k]], (S[x[k]],)), D = eq_var.of(Equal[Variance])
    σ = sqrt(D)
    assert ε > 0
    if n is None:
        n = k
    return Equal(Limit[n:oo](Probability(Abs(ReducedSum(x[:n]) / n - μ) < ε)), 1)


@prove
def prove(Eq):
    from axiom import stats, algebra, calculus

    x = Symbol(real=True, shape=(oo,), random=True)
    μ = Symbol(real=True)
    ε, σ = Symbol(positive=True)
    k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    *Eq[-3:], Eq.hypothesis = apply(Equal(x[k] | x[:k], x[k]), Equal(Expectation(x[k]), μ), Equal(Variance(x[k]), σ ** 2), ε, n)

    Eq << stats.eq_conditioned.imply.eq.var.to.sum.apply(Eq[0], n=n)

    Eq << Eq[-1].this.find(Sum).expr.subs(Eq[2])

    # Eq << Eq.hypothesis.find(ReducedSum / Symbol)
    sample_mean = Eq.hypothesis.find(Mul[ReducedSum])
    Eq << Variance(sample_mean).this.apply(stats.var.to.mul)

    Eq.eq_var = Eq[-1].subs(Eq[-2])

    Eq << Expectation(sample_mean).this.apply(stats.expect.to.mul)

    Eq << Eq[-1].this.rhs.find(ReducedSum).apply(algebra.reducedSum.to.sum, k)

    Eq << Eq[-1].this.find(Expectation[Sum]).apply(stats.expect.sum.to.sum.expect)

    Eq << Eq[-1].subs(Eq[1])

    Eq << stats.eq_expect.eq_var.imply.le.prob.Chebyshev_Inequality.apply(Eq[-1], Eq.eq_var, sqrt(n) * ε / σ)

    Eq << Eq[-1].this.lhs.apply(stats.prob.to.sub.complement)

    Eq << algebra.le.imply.le.transport.apply(Eq[-1], lhs=0)

    Eq << -Eq[-1]

    Eq << calculus.ge.imply.ge.limit.apply(Eq[-1], (n, oo))

    Eq << Eq[-1].this.find(Limit[Mul]).apply(calculus.limit.to.mul)

    Eq << Eq[-1].this.rhs.find(Limit).doit()

    Eq << LessEqual(Eq[-1].find(Probability), 1, plausible=True)

    Eq << calculus.le.imply.le.limit.apply(Eq[-1], (n, oo))

    Eq << algebra.ge.le.imply.eq.apply(Eq[-1], Eq[-3])





if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-04-19
