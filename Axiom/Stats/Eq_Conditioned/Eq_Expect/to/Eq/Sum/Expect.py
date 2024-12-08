from util import *


@apply
def apply(eq_conditioned, eq_expect, j=None, n=None):
    ((x, k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    (S[x[k]], (S[x[k]],)), μ = eq_expect.of(Equal[Expectation])
    if n is None:
        n = k
    assert n > 1
    if j is None:
        j = eq_expect.generate_var(integer=True, var='j')
    return Equal(Sum[j:k, k:n](Expectation(x[j] * x[k])), Binomial(n, 2) * μ ** 2)


@prove
def prove(Eq):
    from Axiom import Discrete, Stats, Algebra

    x = Symbol(real=True, shape=(oo,), random=True)
    μ = Symbol(real=True)
    ε, σ = Symbol(positive=True)
    k, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(Equal(x[k] | x[:k], x[k]), Equal(Expectation(x[k]), μ), j, n)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Stats.Eq_Conditioned.to.Var.eq.Sum.apply(Eq[0], n)

    Eq << Eq[-1].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum, k)

    Eq << Eq[-1].this.lhs.apply(Stats.Var.Sum.eq.Add.Sum, j)

    Eq << Eq[-1].this.find(Covariance).apply(Stats.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.find(Covariance).apply(Stats.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Mul)

    Eq << Eq[-1].subs(Eq[1].subs(k, j))

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Mul)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic).reversed

    # https://en.wikipedia.org/wiki/Bessel's_correction



if __name__ == '__main__':
    run()
# created on 2023-10-12
