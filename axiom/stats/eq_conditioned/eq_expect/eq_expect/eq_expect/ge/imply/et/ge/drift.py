from util import *


@apply
def apply(eq, Q_def, V_def, MDV_def, ge):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    (((S[Q_st_var._subs(a[t].var, a[t])], S[s[t].as_boolean()]), (a, π_quote)), ((), (S[Probability[a:π_quote](a[t] | s[t])], S[Probability[a:π](a[t] | s[t])]), S[Probability[π, π_quote](s[t])], S[Probability[s:π](s[t])])), MDV_st_var = MDV_def.of(Equal[Expectation[Conditioned] - KL * Expr / Expr])
    S[MDV_st_var], S[MDV_st_var._subs(π_quote, π)] = ge.of(Expr >= Expr)
    
    return V_st_var._subs(π, π_quote) >= V_st_var, \
        γ ** Lamda[t](t) @ Expectation[r, a:π_quote](r) >= γ ** Lamda[t](t) @ Expectation[r, a:π](r)


@prove
def prove(Eq):
    from axiom import algebra, keras, stats

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t = Symbol(integer=True) #time step counter
    π, π_quote = Symbol(shape=(D,), real=True) #trainable weights for the agent
    V, Q = Function(real=True, shape=()) #State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    MDV = Function(r'\mathcal{M}_\mathfrak{D}V', real=True, shape=())
    *Eq[-5:], (Eq.ge_VF, Eq.ge_reward) = apply(Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((MDV[π, π_quote] ^ γ)(s[t].var), Expectation[a:π_quote]((Q[π] ^ γ)(s[t].var, a[t]) | s[t]) - Probability[π, π_quote](s[t]) / Probability[s:π](s[t]) * KL(Probability[a:π_quote](a[t] | s[t]), Probability[a:π](a[t] | s[t]))),
                GreaterEqual((MDV[π, π_quote] ^ γ)(s[t].var), (MDV[π, π] ^ γ)(s[t].var)))

    Eq << algebra.ge.given.ge_zero.apply(Eq.ge_VF)

    Eq.VQ, Eq.VV, Eq.QV = keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman.apply(*Eq[:3])

    Eq.Q_quote = Eq[1].subs(π, π_quote)

    Eq.V_quote = Eq[2].subs(π, π_quote)

    Eq.VQ_quote, Eq.VV_quote, Eq.QV_quote = keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman.apply(Eq[0], Eq.Q_quote, Eq.V_quote)

    Eq << Eq[3].subs(π_quote, π)

    Eq << Eq[3] - Eq[-1]

    Eq << algebra.ge.imply.ge_zero.apply(Eq[4])

    Eq << Eq[-1].subs(Eq[-2])

    Eq << algebra.ge.imply.ge.transport.apply(Eq[-1], lhs=0)

    Eq << Eq.QV.subs(a[t].var, a[t])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Expectation).simplify()

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.conditioned.law_of_total_expectation)

    Eq << Eq[-1].this.find(-~Expectation).apply(stats.expect.conditioned.law_of_total_expectation)

    Eq.ge = Eq[-1].subs(Eq.VV.reversed)

    Eq << Eq.VV_quote - Eq.ge.find(Expectation)

    Eq << Eq[-1].this.rhs.apply(stats.add_expect.to.expect)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.mul)

    Eq.ge = Eq.ge + Eq[-1]

    Eq << stats.imply.expect_ge.inf.apply(Eq.ge.find(Expectation))

    Eq << GreaterEqual(γ, 0, plausible=True)

    Eq << algebra.ge_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[-2])

    Eq << -Eq[-1].reversed

    Eq << algebra.ge.ge.imply.ge.add.apply(Eq[-1], Eq.ge)

    Eq << Eq[-1].this.find(Inf).limits_subs(s[t + 1].var, s[t].var)

    Eq << algebra.ge.imply.ge.inf.apply(Eq[-1], (s[t].var,))

    Eq << Eq[-1].this.lhs.apply(algebra.add.to.mul)

    Eq.gt_zero = Greater(1 - γ, 0, plausible=True)

    Eq.ge = algebra.gt_zero.ge.imply.ge.div.apply(Eq.gt_zero, Eq[-1])

    Eq <<= stats.imply.ge_zero.KL.apply(Eq.ge.find(KL)), stats.imply.ge_zero.prob.apply(Eq.ge.find(Probability)), algebra.cond.imply.cond.domain_defined.apply(Eq.ge)

    Eq <<= algebra.ge_zero.ge_zero.imply.ge_zero.apply(Eq[-2], Eq[-3]), algebra.ne_zero.imply.gt_zero.div.apply(Eq[-1])

    Eq << algebra.gt_zero.ge.imply.ge.mul.apply(Eq[-1], Eq[-2])

    Eq << algebra.cond.imply.all.apply(Eq[-1], s[t].var, simplify=None)

    Eq << algebra.all_ge.imply.inf_ge.apply(Eq[-1])

    Eq << algebra.gt_zero.ge.imply.ge.div.apply(Eq.gt_zero, Eq[-1])

    Eq << algebra.ge.ge.imply.ge.transit.apply(Eq.ge, Eq[-1])

    Eq << algebra.inf_ge.imply.all_ge.apply(Eq[-1])

    Eq <<= Eq[2].subs(s[t].var, s[t]).subs(t, 0), Eq.V_quote.subs(s[t].var, s[t]).subs(t, 0)

    Eq <<= stats.eq.imply.eq.expect.apply(Eq[-2]), stats.eq.imply.eq.expect.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(MatMul).apply(stats.matmul.to.expect), Eq[-1].this.find(MatMul).apply(stats.matmul.to.expect)

    Eq <<= Eq[-2].this.rhs.apply(stats.expect.law_of_total_expectation), Eq[-1].this.rhs.apply(stats.expect.law_of_total_expectation)

    Eq <<= Eq[-2].this.rhs.apply(stats.expect.to.matmul), Eq[-1].this.rhs.apply(stats.expect.to.matmul)

    Eq << Eq.ge_VF.subs(t, 0)

    Eq << stats.ge.imply.ge.expect.apply(Eq[-1], (s[0],))

    Eq << Eq[-1].subs(Eq[-3], Eq[-4])

    #https://arxiv.org/pdf/2201.02373.pdf
    #https://arxiv.org/pdf/2211.11030.pdf
    #https://arxiv.org/pdf/2205.01447.pdf
    #https://arxiv.org/pdf/2210.05639.pdf
    
    


if __name__ == '__main__':
    run()
# created on 2023-04-20
# updated on 2023-04-24
