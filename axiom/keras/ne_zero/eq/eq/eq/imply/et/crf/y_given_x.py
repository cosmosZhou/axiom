from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption):
    from axiom.keras.ne_zero.eq.eq.eq.imply.eq.crf.markov import process_assumptions
    x, y = process_assumptions(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption)
    n, d = x.shape

    t = Symbol(domain=Range(n))
    i = Symbol(integer=True)

    joint_probability = Probability(x[:t + 1], y[:t + 1])
    emission_probability = Probability(x[i] | y[i])
    transition_probability = Probability(y[i] | y[i - 1])
    y_given_x_probability = Probability(y | x)
    y = pspace(y).symbol

    G = Symbol(Lamda[y[i - 1], y[i]](log(transition_probability)))

    s = Symbol(Lamda[t](log(joint_probability)))

    x = Symbol(Lamda[y[i], i](log(emission_probability)))

    z = Symbol(Lamda[y[t], t](Sum[y[:t]](E ** s[t])))

    x_quote = Symbol(Lamda[t](log(z[t])))

    return Infer(t > 0, Equal(x_quote[t], logsumexp(x_quote[t - 1] + G) + x[t])), \
        Equal(-log(y_given_x_probability), logsumexp(x_quote[n - 1]) - s[n - 1])


@prove
def prove(Eq):
    from axiom import keras, algebra, sets, discrete, stats

    from axiom.keras.ne_zero.eq.eq.eq.imply.eq.crf.markov import markov_assumptions
    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True)
    Eq << apply(*markov_assumptions(x, y))

    x_probability = Eq[3].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq[4].lhs.args
    Eq.z_definition = Eq[5].apply(algebra.eq.imply.eq.lamda, (Eq[5].lhs.indices[-1],))

    Eq << keras.ne_zero.eq.eq.eq.imply.eq.crf.markov.apply(*Eq[:4])

    Eq << keras.eq.imply.infer.crf.logits.apply(Eq[-1], Eq[8].lhs.base, Eq[7].lhs.base, s)

    Eq << Eq[-2].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(sets.notin.imply.notin.sub, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq << Eq.z_definition.subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.notin.sub, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs.rhs)

    Eq << Eq[-1].this.find(Exp).apply(algebra.exp.to.mul)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.pop.slice)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.reducedSum)

    Eq << Eq[-1].this.find(Lamda).apply(discrete.lamda.reducedSum.to.matmul)

    Eq.z_recursion = Eq[-1].subs(Eq.z_definition.reversed)

    Eq << Eq[6].subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.notin.sub, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq <<= Eq.z_recursion & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs.rhs)

    Eq << Eq[-1].this.find(Log).apply(algebra.log.to.add)

    Eq.z_definition_by_x_quote = algebra.eq.imply.eq.exp.apply(Eq[6].reversed)

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.exp)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.find(NotElement).apply(sets.notin.imply.notin.add, 1)

    Eq << algebra.ou.imply.infer.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.ne_zero.given.gt_zero)

    Eq << Eq[-1].this.find(log).apply(keras.log.reducedSum.to.logsumexp)

    Eq.xy_joint_nonzero = stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[3], (slice(0, t + 1), slice(0, t + 1)))

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq.xy_joint_nonzero)

    y = Eq[-1].lhs.arg.lhs.base
    Eq << stats.ne_zero.imply.eq.prob.to.mul.prob.bayes.apply(Eq[-2], y[:t + 1])

    Eq << stats.sum.to.prob.apply(Sum[pspace(y[:t + 1]).symbol](Eq[-1].lhs))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(algebra.eq.imply.ou.log)

    Eq << algebra.et.imply.et.apply(Eq[-1] & Eq.xy_joint_nonzero)

    Eq << Eq[-1].this.rhs.apply(algebra.log.to.add)

    Eq << algebra.eq.imply.eq.exp.apply(Eq[4].reversed)

    Eq.y_given_x_log = Eq[-2].subs(Eq[-1])

    Eq << Eq.z_definition.apply(algebra.eq.imply.eq.reducedSum)

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq.y_given_x_log.subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)

    Eq << Eq[10].this.rhs.args[1].defun().reversed

    Eq << Eq[-1] + Eq[-2]

    # reference: Neural Architectures for Named Entity Recognition.pdf
    # https://spaces.ac.cn/archives/5542




if __name__ == '__main__':
    run()
# created on 2018-12-21
# updated on 2023-05-20
