from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, y):
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Probability[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Probability[Equal], 0])
    
    return GreaterEqual(KL(Probability(Equal(x_lhs, x_var) & Equal(y, y.var), *weights_lhs), Probability(Equal(x_rhs, x_var) & Equal(y, y.var), *weights_rhs)),
                        KL(Probability(Equal(x_lhs, x_var), *weights_lhs), Probability(Equal(x_rhs, x_var), *weights_rhs)))

@prove
def prove(Eq):
    from axiom import stats, algebra

    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True, shape=(m,))
    y = Symbol(random=True, integer=True, shape=(n,))
    Eq << apply(Unequal(Probability[θ](x), 0),
                Unequal(Probability[θ_quote](x), 0), y)

    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.sum, order=lambda s : str(s))

    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.sum)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[0], y, spread_weight=True)

    Eq << stats.ne_zero.imply.eq.bayes.apply(Eq[1], y, spread_weight=True)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.find(Log).apply(algebra.log.to.add, pivot=2)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Probability[Conditioned]]).apply(stats.sum.to.one.conditioned)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.swap)

    Eq << Eq[-1].this.lhs.apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Mul[~Sum]]).apply(stats.sum.to.KL)

    Eq << stats.imply.ge_zero.conditioned.KL.apply(*Eq[-1].find(KL).args)

    Eq << algebra.ge_zero.imply.ge_zero.mul.apply(Eq[-1], Probability[θ](Equal(x, x.var)))

    Eq << algebra.ge_zero.imply.ge_zero.sum.apply(Eq[-1], (x.var,))

    
    


if __name__ == '__main__':
    run()
# created on 2021-07-23
# updated on 2023-05-18
from . import pdf
