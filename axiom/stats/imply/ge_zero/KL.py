from util import *


def kull_back(p, q):
    cond_p = p.of(Probability)
    cond_q = q.of(Probability)
    if cond_p.is_Equal:
        X, x = cond_p.args
        _X, _x = cond_q.of(Equal)
        assert x == _x
        return Sum[x](p * log(p / q))
    elif cond_p.is_Conditioned:
        cond_p, given = cond_p.args
        cond_q, _given = cond_q.of(Conditioned)
        if cond_p.is_Equal:
            X, x = cond_p.args
            _X, _x = cond_q.of(Equal)
            assert x == _x
            return Sum[x](p * log(p / q))
    else:
        conds_p = cond_p.of(And)
        conds_q = cond_q.of(And)

        symbol2value = {}
        for cond in conds_p:
            X, x = cond.of(Equal)
            symbol2value[x] = X

        for cond in conds_q:
            X, x = cond.of(Equal)
            assert x in symbol2value

        return Sum[tuple(symbol2value.keys())](p * log(p / q))


@apply
def apply(prob_lhs, prob_rhs):
    (x, x_var), *weights_lhs = prob_lhs.of(Probability[Equal])
    (x_quote, S[x_var]), *weights_rhs = prob_rhs.of(Probability[Equal])
    return GreaterEqual(KL(prob_lhs, prob_rhs), 0, evaluate=False)


@prove
def prove(Eq):
    from axiom import stats, algebra

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(Probability[θ](x), Probability[θ_quote](x))

    Eq << Eq[-1].this.find(KL).apply(stats.KL.to.sum)

    Eq << algebra.imply.ge.log.apply(Eq[1].find(Log).arg)

    Eq << algebra.ge.imply.ge.mul.apply(Eq[-1], Eq[1].find(Probability))

    x = Eq[1].lhs.variable
    Eq << algebra.ge.imply.ge.sum.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one)

    Eq << Eq[-1].this.rhs.find(Sum).apply(stats.sum.to.one)
    


if __name__ == '__main__':
    run()

# created on 2021-07-20
# updated on 2023-03-25
