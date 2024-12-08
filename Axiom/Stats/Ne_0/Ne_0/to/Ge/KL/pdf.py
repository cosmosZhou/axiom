from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, y):
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Probability[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Probability[Equal], 0])

    return GreaterEqual(KL(Probability(Equal(x_lhs, x_var) & Equal(y, y.var), *weights_lhs), Probability(Equal(x_rhs, x_var) & Equal(y, y.var), *weights_rhs)),
                        KL(Probability(Equal(x_lhs, x_var), *weights_lhs), Probability(Equal(x_rhs, x_var), *weights_rhs)))

@prove
def prove(Eq):
    from Axiom import Stats, Algebra, Calculus


    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True, shape=(m,))
    y = Symbol(random=True, real=True, shape=(n,))
    Eq << apply(Unequal(Probability[θ](x), 0),
                Unequal(Probability[θ_quote](x), 0), y)

    Eq << Eq[-1].this.find(KL).apply(Stats.KL.eq.Integral, order=lambda s : str(s))

    Eq << Eq[-1].this.find(KL).apply(Stats.KL.eq.Integral)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[0], y, spread_weight=True)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[1], y, spread_weight=True)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.find(Log).apply(Algebra.Log.eq.Add, pivot=2)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.lhs.args[1].apply(Calculus.Integral.limits.swap)

    Eq << Eq[-1].this.lhs.args[1].apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability[Conditioned]]).apply(Stats.Integral.eq.One.Conditioned)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.swap)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Mul[~Integral]]).apply(Stats.Integral.eq.KL)

    Eq << Stats.KLProbSConditioned.ge.Zero.apply(*Eq[-1].find(KL).args)

    Eq << Algebra.Ge_0.to.Ge_0.Mul.apply(Eq[-1], Probability[θ](Equal(x, x.var)))

    Eq << Calculus.Ge_0.to.Ge_0.Integral.apply(Eq[-1], (x.var,))





if __name__ == '__main__':
    run()
# created on 2023-03-25
# updated on 2023-03-26
