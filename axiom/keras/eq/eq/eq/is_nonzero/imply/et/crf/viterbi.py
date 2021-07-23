from util import *


@apply
def apply(*given):
    from axiom.keras.eq.eq.eq.is_nonzero.imply.eq.crf.markov import process_assumptions
    x, y = process_assumptions(*given)

    n, d = x.shape
    t = Symbol.t(domain=Range(0, n))
    i = Symbol.i(integer=True)

    joint_probability_t = Probability(x[:t + 1], y[:t + 1])
    joint_probability = Probability(x, y)
    emission_probability = Probability(x[i] | y[i])
    transition_probability = Probability(y[i] | y[i - 1])
    y = pspace(y).symbol

    G = Symbol.G(Lamda[y[i - 1], y[i]](-log(transition_probability)))
    assert G.shape == (d, d)
    s = Symbol.s(Lamda[t](-log(joint_probability_t)))
    assert s.shape == (n,)
    x = Symbol.x(Lamda[y[i], i](-log(emission_probability)))
    assert x.shape == (n, d)
    x_quote = Symbol.x_quote(Lamda[y[t], t](Minimize[y[:t]](s[t])))
    assert x_quote.shape == (n, d)

    assert x_quote.is_real
    return Suffice(t > 0, Equal(x_quote[t], x[t] + ReducedMin(x_quote[t - 1] + G))), \
        Equal(Maximize[y](joint_probability), exp(-ReducedMin(x_quote[n - 1])))


@prove
def prove(Eq):
    from axiom import keras, algebra, sets

    from axiom.keras.eq.eq.eq.is_nonzero.imply.eq.crf.markov import assumptions
    Eq << apply(*assumptions())

    x_probability = Eq[3].lhs.arg.args[0]
    x = x_probability.lhs
    n = x.shape[0]
    s, t = Eq[4].lhs.args
    Eq.x_quote_definition = Eq[5].apply(algebra.eq.imply.eq.lamda, (Eq[5].lhs.indices[-1],), simplify=False)

    y = Eq.x_quote_definition.rhs.variable.base
    Eq << keras.eq.eq.eq.is_nonzero.imply.eq.crf.markov.apply(*Eq[:4])

    Eq << keras.eq.imply.suffice.crf.logits.apply(Eq[-1], Eq[7].lhs.base, Eq[6].lhs.base, s)

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.args[1].apply(sets.notcontains.imply.notcontains.sub, 1)

    Eq << algebra.ou.imply.suffice.apply(Eq[-1], 1)

    Eq << Eq.x_quote_definition.subs(t, t + 1)

    Eq << Eq[-1].this.args[0].apply(sets.notcontains.imply.notcontains.sub, 1)

    Eq << algebra.ou.imply.suffice.apply(Eq[-1])

    Eq <<= Eq[-1] & Eq[-4]

    Eq << Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs.rhs)

    Eq << Eq[-1].this.rhs.rhs.expr.simplify()

    Eq << Eq[-1].this.rhs.rhs.args[1].expr.apply(algebra.minimize.limits.split.slice.pop_back)
    Eq << Eq[-1].this.rhs.rhs.args[1].expr.simplify()

    Eq << Eq[-1].this.rhs.rhs.args[1].expr.apply(algebra.minimize.to.lamda)

    Eq << Eq[-1].this.rhs.rhs.args[1].apply(algebra.lamda.to.reducedMin)

    Eq << Eq[-1].subs(Eq.x_quote_definition.reversed)

    Eq << Eq[-1].subs(t, t - 1)

    Eq << Eq[-1].this.args[0].apply(sets.notcontains.imply.notcontains.add, 1)

    Eq << algebra.ou.imply.suffice.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(algebra.is_nonzero.given.is_positive)

    Eq << -Eq[4].reversed

    Eq << Eq[-1].apply(algebra.eq.imply.eq.exp)

    Eq << algebra.eq.imply.eq.maximize.apply(Eq[-1], (y[:t + 1],))

    Eq << Eq[-1].this.rhs.apply(algebra.maximize.to.exp)

    Eq << algebra.eq.imply.eq.reducedMin.apply(Eq.x_quote_definition).this.rhs.simplify(wrt=t)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].subs(t, n - 1)


if __name__ == '__main__':
    run()