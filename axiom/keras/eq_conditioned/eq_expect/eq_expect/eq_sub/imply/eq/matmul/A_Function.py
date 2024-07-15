from util import *


@apply
def apply(eq, Q_def, V_def, A_def, π_quote=None):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var, A_st_var = extract_QVA(eq, Q_def, V_def, A_def)
    assert π_quote.shape == π.shape
    return Equal(γ ** Lamda[t](t) @ (Expectation[r, a:π_quote](r) - Expectation[r, a:π](r)),
                 γ ** Lamda[t](t) @ Lamda[t](Expectation[a:π_quote, s]((A_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t])))))


@prove
def prove(Eq):
    from axiom import keras, stats, discrete, algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π, π_quote = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q, A = Function(real=True, shape=()) # State-Value Function, Action-Value Function, Advantage Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-4:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((A[π] ^ γ)(s[t].var, a[t].var), (Q[π] ^ γ)(s[t].var, a[t].var) - (V[π] ^ γ)(s[t].var)),
                π_quote)

    Eq << keras.eq_conditioned.eq_expect.eq_expect.eq_sub.imply.eq.expect.temporal_difference_residual.apply(*Eq[:4]).reversed

    Eq << Eq[-1].subs(s[t].var, s[t]).subs(a[t].var, a[t])

    Eq << Eq.hypothesis.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Lamda).apply(stats.lamda.expect.to.expect.lamda)

    Eq << Eq[-1].this.rhs.apply(stats.matmul.to.expect)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.rhs.find(Mul[Expectation]).apply(stats.mul.to.expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Symbol * Pow).args[:2].apply(algebra.mul.to.pow.add.exponent)

    Eq << Eq[-1].this.rhs.find(Sum[~Expectation]).apply(stats.expect.to.add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.rhs.find(Expectation[Conditioned[Pow * Function]]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[-Sum]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Expectation[Sum[Expectation]]).apply(stats.expect.sum.to.sum.expect)

    Eq << Eq[-1].this.find(Sum[~Expectation]).simplify()

    Eq << Eq[-1].this.find(Sum[~Expectation]).apply(stats.expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Sum[Expectation]).apply(stats.sum.expect.to.expect.sum)

    Eq << Eq[-1].this.find(Expectation[~Sum]).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.find(Expectation[MatMul]).apply(stats.expect.to.matmul)

    Eq << Eq[-1].this.find(Expectation[Sum]).apply(stats.expect.sum.to.sum.expect)

    Eq << Eq[-1].this.find(Sum[~Expectation]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Sum[Mul[~Expectation]]).simplify()

    Eq << Eq[-1].this.find(Sum[Mul[~Expectation]]).apply(stats.expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.limits.subs.offset, -1)

    Eq << Eq[-1].this.find(Expectation[Sum]).apply(stats.expect.sum.to.sum.expect)

    Eq << Eq[-1].this.find(Sum[~Expectation]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(-~Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[2].subs(s[t].var, s[t]).subs(t, 0)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Expectation[MatMul]).apply(stats.expect.to.matmul)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(stats.expect.law_of_total_expectation)

    Eq << Eq[-1].this.rhs.find(MatMul[~Lamda]).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.rhs.apply(discrete.add.to.matmul)

    # https://arxiv.org/pdf/1502.05477.pdf#page=10




if __name__ == '__main__':
    run()
# created on 2023-04-12
# updated on 2023-05-20
