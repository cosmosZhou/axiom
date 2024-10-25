from util import *


@apply
def apply(prob_lhs, prob_rhs):
    (x_eq, y_eq), *weights_lhs = prob_lhs.of(Probability[Conditioned])
    (S[x_eq], S[y_eq]), *weights_rhs = prob_rhs.of(Probability[Conditioned])
    return GreaterEqual(KL(prob_lhs, prob_rhs), 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import stats, algebra

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True, shape=(m,))
    y = Symbol(random=True, integer=True, shape=(n,))
    Eq << apply(Probability[θ](x | y), Probability[θ_quote](x | y))

    Eq << Eq[0].this.find(KL).apply(stats.KL.to.sum)

    Eq << algebra.then.ge.log.apply(Eq[1].find(Log).arg)

    Eq << algebra.ge.then.ge.mul.apply(Eq[-1], Eq[1].find(Probability))

    Eq << algebra.ge.then.ge.sum.apply(Eq[-1], (x.var,))

    Eq << Eq[-1].this.rhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one.conditioned)

    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one.conditioned)





if __name__ == '__main__':
    run()
# created on 2021-07-19
# updated on 2023-03-26
