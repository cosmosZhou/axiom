from util import *


@apply
def apply(prob_lhs, prob_rhs):
    (x_eq, y_eq), *weights_lhs = prob_lhs.of(Probability[Conditioned])
    (S[x_eq], S[y_eq]), *weights_rhs = prob_rhs.of(Probability[Conditioned])
    return GreaterEqual(KL(prob_lhs, prob_rhs), 0, evaluate=False)


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True, shape=(m,))
    y = Symbol(random=True, integer=True, shape=(n,))
    Eq << apply(Probability[θ](x | y), Probability[θ_quote](x | y))

    Eq << Eq[0].this.find(KL).apply(Stats.KL.eq.Sum)

    Eq << Algebra.Log.ge.Sub_.One.Inv.apply(Eq[1].find(Log).arg)

    Eq << Algebra.Ge.to.Ge.Mul.apply(Eq[-1], Eq[1].find(Probability))

    Eq << Algebra.Ge.to.Ge.Sum.apply(Eq[-1], (x.var,))

    Eq << Eq[-1].this.rhs.expr.apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Stats.Sum.eq.One.Conditioned)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Stats.Sum.eq.One.Conditioned)





if __name__ == '__main__':
    run()
# created on 2021-07-19
# updated on 2023-03-26
