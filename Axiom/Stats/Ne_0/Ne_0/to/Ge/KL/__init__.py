from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, y):
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Probability[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Probability[Equal], 0])

    return GreaterEqual(KL(Probability(Equal(x_lhs, x_var) & Equal(y, y.var), *weights_lhs), Probability(Equal(x_rhs, x_var) & Equal(y, y.var), *weights_rhs)),
                        KL(Probability(Equal(x_lhs, x_var), *weights_lhs), Probability(Equal(x_rhs, x_var), *weights_rhs)))

@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True, shape=(m,))
    y = Symbol(random=True, integer=True, shape=(n,))
    Eq << apply(Unequal(Probability[θ](x), 0),
                Unequal(Probability[θ_quote](x), 0), y)

    Eq << Eq[-1].this.find(KL).apply(Stats.KL.eq.Sum, order=lambda s : str(s))

    Eq << Eq[-1].this.find(KL).apply(Stats.KL.eq.Sum)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[0], y, spread_weight=True)

    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[1], y, spread_weight=True)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.find(Log).apply(Algebra.Log.eq.Add, pivot=2)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Sum.limits.swap)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Probability[Conditioned]]).apply(Stats.Sum.eq.One.Conditioned)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Mul[~Sum]]).apply(Stats.Sum.eq.KL)

    Eq << Stats.KLProbSConditioned.ge.Zero.apply(*Eq[-1].find(KL).args)

    Eq << Algebra.Ge_0.to.Ge_0.Mul.apply(Eq[-1], Probability[θ](Equal(x, x.var)))

    Eq << Algebra.Ge_0.to.Ge_0.Sum.apply(Eq[-1], (x.var,))





if __name__ == '__main__':
    run()
# created on 2021-07-23
# updated on 2023-05-18
from . import pdf
