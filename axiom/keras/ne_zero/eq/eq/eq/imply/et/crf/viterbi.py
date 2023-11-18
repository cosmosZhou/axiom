from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption):
    from axiom.keras.ne_zero.eq.eq.eq.imply.eq.crf.markov import process_assumptions
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)

    n, d = x.shape
    t = Symbol(domain=Range(n))
    i = Symbol(integer=True)

    joint_probability_t = Probability(x[:t + 1], y[:t + 1])
    joint_probability = Probability(x, y)
    emission_probability = Probability(x[i] | y[i])
    transition_probability = Probability(y[i] | y[i - 1])
    y = pspace(y).symbol

    G = Symbol(Lamda[y[i - 1], y[i]](log(transition_probability)))

    s = Symbol(Lamda[t](log(joint_probability_t)))

    x = Symbol(Lamda[y[i], i](log(emission_probability)))

    x_quote = Symbol(Lamda[y[t], t](Maxima[y[:t]](s[t])))

    return Infer(t > 0, Equal(x_quote[t], x[t] + ReducedMax(x_quote[t - 1] + G))), \
        Equal(Maxima[y](joint_probability), exp(ReducedMax(x_quote[n - 1])))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    from axiom.keras.ne_zero.eq.eq.eq.imply.eq.crf.markov import markov_assumptions
    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True)
    Eq[-4:], (*Eq[-3:], Eq.G_definition), Eq[-2:] = apply(*markov_assumptions(x, y))

    x_probability = Eq[3].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq[4].lhs.args
    Eq.x_quote_definition = Eq[5].apply(algebra.eq.imply.eq.lamda, (Eq[5].lhs.indices[-1],))

    y = Eq.x_quote_definition.rhs.variable.base
    Eq << keras.ne_zero.eq.eq.eq.imply.eq.crf.markov.apply(*Eq[:4])

    Eq << keras.eq.imply.infer.crf.logits.apply(Eq[-1], Eq.G_definition.lhs.base, Eq[6].lhs.base, s)

    Eq << Eq[-2].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(sets.notin.imply.notin.sub, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.notin.sub, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs.rhs)

    Eq << Eq[-1].this.find(Maxima).apply(algebra.maxima.limits.pop.slice)

    Eq << Eq[-1].this.find(Maxima).simplify()

    Eq << Eq[-1].this.find(Maxima).apply(algebra.maxima.to.reducedMax)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.to.reducedMax)

    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.notin.add, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.given.gt_zero)

    Eq << Eq[4].reversed

    Eq << Eq[-1].apply(algebra.eq.imply.eq.exp)

    Eq << algebra.eq.imply.eq.maxima.apply(Eq[-1], (y[:t + 1],))

    Eq << Eq[-1].this.rhs.apply(algebra.maxima.to.exp)

    Eq << algebra.eq.imply.eq.reducedMax.apply(Eq.x_quote_definition)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)

    #https://arxiv.org/abs/1603.01360



if __name__ == '__main__':
    run()

# created on 2020-12-20
# updated on 2023-05-20
