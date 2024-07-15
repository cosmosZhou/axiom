from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, y):
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Probability[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Probability[Equal], 0])

    return GreaterEqual(KL(Probability(Equal(x_lhs, x_var) & Equal(y, y.var), *weights_lhs), Probability(Equal(x_rhs, x_var) & Equal(y, y.var), *weights_rhs)),
                        KL(Probability(Equal(x_lhs, x_var), *weights_lhs), Probability(Equal(x_rhs, x_var), *weights_rhs)))

@prove
def prove(Eq):
    from axiom import stats, algebra, calculus


    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True, shape=(m,))
    y = Symbol(random=True, real=True, shape=(n,))
    Eq << apply(Unequal(Probability[θ](x), 0),
                Unequal(Probability[θ_quote](x), 0), y)

    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.integral, order=lambda s : str(s))

    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.integral)

    Eq << stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[0], y, spread_weight=True)

    Eq << stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[1], y, spread_weight=True)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.find(Log).apply(algebra.log.to.add, pivot=2)

    Eq << Eq[-1].this.lhs.expr.apply(algebra.mul.to.add)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.to.add)

    Eq << Eq[-1].this.lhs.args[1].apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.lhs.args[1].apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability[Conditioned]]).apply(stats.integral.to.one.conditioned)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.lhs.apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Mul[~Integral]]).apply(stats.integral.to.KL)

    Eq << stats.imply.ge_zero.conditioned.KL.apply(*Eq[-1].find(KL).args)

    Eq << algebra.ge_zero.imply.ge_zero.mul.apply(Eq[-1], Probability[θ](Equal(x, x.var)))

    Eq << calculus.ge_zero.imply.ge_zero.integral.apply(Eq[-1], (x.var,))





if __name__ == '__main__':
    run()
# created on 2023-03-25
# updated on 2023-03-26
