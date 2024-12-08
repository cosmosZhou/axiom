from util import *


@apply
def apply(x_independence_assumption, y_independence_assumption, xy_independence_assumption, xy_nonzero_assumption):
    from Axiom.Keras.Ne_0.Eq.Eq.Eq.to.Eq.crf.markov import process_assumptions
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

    return Imply(t > 0, Equal(x_quote[t], logsumexp(x_quote[t - 1] + G) + x[t])), \
        Equal(-log(y_given_x_probability), logsumexp(x_quote[n - 1]) - s[n - 1])


@prove
def prove(Eq):
    from Axiom import Keras, Algebra, Sets, Discrete, Stats

    from Axiom.Keras.Ne_0.Eq.Eq.Eq.to.Eq.crf.markov import markov_assumptions
    d, n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n, d), real=True, random=True)
    y = Symbol(shape=(n,), domain=Range(d), random=True)
    Eq << apply(*markov_assumptions(x, y))

    x_probability = Eq[3].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq[4].lhs.args
    Eq.z_definition = Eq[5].apply(Algebra.Eq.to.Eq.Lamda, (Eq[5].lhs.indices[-1],))

    Eq << Keras.Ne_0.Eq.Eq.Eq.to.Eq.crf.markov.apply(*Eq[:4])

    Eq << Keras.Eq.to.Imply.crf.logits.apply(Eq[-1], Eq[8].lhs.base, Eq[7].lhs.base, s)

    Eq << Eq[-2].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(Sets.NotIn.to.NotIn.Sub, 1)

    Eq << Algebra.Or.to.Imply.apply(Eq[-1])

    Eq << Eq.z_definition.subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.NotIn.Sub, 1)

    Eq << Algebra.Or.to.Imply.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs.rhs)

    Eq << Eq[-1].this.find(Exp).apply(Algebra.Exp.eq.Mul)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.pop.Slice)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.ReducedSum)

    Eq << Eq[-1].this.find(Lamda).apply(Discrete.Lamda.ReducedSum.eq.Dot)

    Eq.z_recursion = Eq[-1].subs(Eq.z_definition.reversed)

    Eq << Eq[6].subs(t, t + 1)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.NotIn.Sub, 1)

    Eq << Algebra.Or.to.Imply.apply(Eq[-1])

    Eq <<= Eq.z_recursion & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs.rhs)

    Eq << Eq[-1].this.find(Log).apply(Algebra.Log.eq.Add)

    Eq.z_definition_by_x_quote = Algebra.Eq.to.Eq.Exp.apply(Eq[6].reversed)

    Eq << Eq[-1].subs(Eq.z_definition_by_x_quote)

    Eq << Eq[-1].this.find(MatMul).apply(Discrete.Dot.eq.Exp)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.find(NotElement).apply(Sets.NotIn.to.NotIn.Add, 1)

    Eq << Algebra.Or.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne_0.of.Gt_0)

    Eq << Eq[-1].this.find(log).apply(Keras.Log.ReducedSum.eq.LogSumExp)

    Eq.xy_joint_nonzero = Stats.Ne_0.to.Ne_0.joint_slice.apply(Eq[3], (slice(0, t + 1), slice(0, t + 1)))

    Eq << Stats.Ne_0.to.And.Ne_0.apply(Eq.xy_joint_nonzero)

    y = Eq[-1].lhs.arg.lhs.base
    Eq << Stats.Ne_0.to.Prob.eq.Mul.Prob.bayes.apply(Eq[-2], y[:t + 1])

    Eq << Stats.Sum.eq.Prob.apply(Sum[pspace(y[:t + 1]).symbol](Eq[-1].lhs))

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(Algebra.Eq.to.Or.Log)

    Eq << Algebra.And.to.And.apply(Eq[-1] & Eq.xy_joint_nonzero)

    Eq << Eq[-1].this.rhs.apply(Algebra.Log.eq.Add)

    Eq << Algebra.Eq.to.Eq.Exp.apply(Eq[4].reversed)

    Eq.y_given_x_log = Eq[-2].subs(Eq[-1])

    Eq << Eq.z_definition.apply(Algebra.Eq.to.Eq.ReducedSum)

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
