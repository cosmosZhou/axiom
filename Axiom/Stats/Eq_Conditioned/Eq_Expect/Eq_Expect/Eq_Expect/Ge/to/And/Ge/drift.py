from util import *


@apply
def apply(eq, Q_def, V_def, MDV_def, ge):
    from Axiom.Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    (((S[Q_st_var._subs(a[t].var, a[t])], S[s[t].as_boolean()]), (a, π_quote)), ((S[Probability[a:π_quote](a[t] | s[t])], S[Probability[a:π](a[t] | s[t])]), S[Probability[π, π_quote](s[t])], S[Probability[s:π](s[t])])), MDV_st_var = MDV_def.of(Equal[Expectation[Conditioned] - KL * Expr / Expr])
    S[MDV_st_var], S[MDV_st_var._subs(π_quote, π)] = ge.of(Expr >= Expr)

    return V_st_var._subs(π, π_quote) >= V_st_var, \
        γ ** Lamda[t](t) @ Expectation[r, a:π_quote](r) >= γ ** Lamda[t](t) @ Expectation[r, a:π](r)


@prove
def prove(Eq):
    from Axiom import Algebra, Keras, Stats

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True) # time step counter
    π, π_quote = Symbol(shape=(D,), real=True) # trainable weights for the agent
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    MDV = Function(r'\mathcal{M}_\mathfrak{D}V', real=True, shape=())
    *Eq[-5:], (Eq.ge_VF, Eq.ge_reward) = apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((MDV[π, π_quote] ^ γ)(s[t].var), Expectation[a:π_quote]((Q[π] ^ γ)(s[t].var, a[t]) | s[t]) - Probability[π, π_quote](s[t]) / Probability[s:π](s[t]) * KL(Probability[a:π_quote](a[t] | s[t]), Probability[a:π](a[t] | s[t]))),
                GreaterEqual((MDV[π, π_quote] ^ γ)(s[t].var), (MDV[π, π] ^ γ)(s[t].var)))

    Eq << Algebra.Ge.of.Ge_0.apply(Eq.ge_VF)

    Eq.VQ, Eq.VV, Eq.QV = Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman.apply(*Eq[:3])

    Eq.Q_quote = Eq[1].subs(π, π_quote)

    Eq.V_quote = Eq[2].subs(π, π_quote)

    Eq.VQ_quote, Eq.VV_quote, Eq.QV_quote = Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman.apply(Eq[0], Eq.Q_quote, Eq.V_quote)

    Eq << Eq[3].subs(π_quote, π)

    Eq << Eq[3] - Eq[-1]

    Eq << Algebra.Ge.to.Ge_0.apply(Eq[4])

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Algebra.Ge.to.Ge.transport.apply(Eq[-1], lhs=0)

    Eq << Eq.QV.subs(a[t].var, a[t])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Expectation).simplify()

    Eq << Eq[-1].this.find(Expectation).apply(Stats.Expect.Conditioned.law_of_total_expectation)

    Eq << Eq[-1].this.find(-~Expectation).apply(Stats.Expect.Conditioned.law_of_total_expectation)

    Eq.ge = Eq[-1].subs(Eq.VV.reversed)

    Eq << Eq.VV_quote - Eq.ge.find(Expectation)

    Eq << Eq[-1].this.rhs.apply(Stats.Add.Expect.eq.Expect)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Stats.Expect.eq.Mul)

    Eq.ge = Eq.ge + Eq[-1]

    Eq << Stats.Expect.ge.Inf.apply(Eq.ge.find(Expectation))

    Eq << GreaterEqual(γ, 0, plausible=True)

    Eq << Algebra.Ge_0.Ge.to.Ge.Mul.apply(Eq[-1], Eq[-2])

    Eq << -Eq[-1].reversed

    Eq << Algebra.Ge.Ge.to.Ge.Add.apply(Eq[-1], Eq.ge)

    Eq << Eq[-1].this.find(Inf).limits_subs(s[t + 1].var, s[t].var)

    Eq << Algebra.Ge.to.Ge.Inf.apply(Eq[-1], (s[t].var,))

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Mul)

    Eq.gt_zero = Greater(1 - γ, 0, plausible=True)

    Eq.ge = Algebra.Gt_0.Ge.to.Ge.Div.apply(Eq.gt_zero, Eq[-1])

    Eq <<= Stats.KL.ge.Zero.apply(Eq.ge.find(KL)), Stats.Prob.ge.Zero.apply(Eq.ge.find(Probability)), Algebra.Cond.to.Cond.domain_defined.apply(Eq.ge)

    Eq <<= Algebra.Ge_0.Ge_0.to.Ge_0.apply(Eq[-2], Eq[-3]), Algebra.Ne_0.to.Gt_0.Div.apply(Eq[-1])

    Eq << Algebra.Gt_0.Ge.to.Ge.Mul.apply(Eq[-1], Eq[-2])

    Eq << Algebra.Cond.to.All.apply(Eq[-1], s[t].var, simplify=None)

    Eq << Algebra.All_Ge.to.GeInf.apply(Eq[-1])

    Eq << Algebra.Gt_0.Ge.to.Ge.Div.apply(Eq.gt_zero, Eq[-1])

    Eq << Algebra.Ge.Ge.to.Ge.trans.apply(Eq.ge, Eq[-1])

    Eq << Algebra.GeInf.to.All.Ge.apply(Eq[-1])

    Eq <<= Eq[2].subs(s[t].var, s[t]).subs(t, 0), Eq.V_quote.subs(s[t].var, s[t]).subs(t, 0)

    Eq <<= Stats.Eq.to.Eq.Expect.apply(Eq[-2]), Stats.Eq.to.Eq.Expect.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(MatMul).apply(Stats.Dot.eq.Expect), Eq[-1].this.find(MatMul).apply(Stats.Dot.eq.Expect)

    Eq <<= Eq[-2].this.rhs.apply(Stats.Expect.law_of_total_expectation), Eq[-1].this.rhs.apply(Stats.Expect.law_of_total_expectation)

    Eq <<= Eq[-2].this.rhs.apply(Stats.Expect.eq.Dot), Eq[-1].this.rhs.apply(Stats.Expect.eq.Dot)

    Eq << Eq.ge_VF.subs(t, 0)

    Eq << Stats.Ge.to.Ge.Expect.apply(Eq[-1], (s[0],))

    Eq << Eq[-1].subs(Eq[-3], Eq[-4])

    # https://arxiv.org/pdf/2201.02373.pdf
    # https://arxiv.org/pdf/2211.11030.pdf
    # https://arxiv.org/pdf/2205.01447.pdf
    # https://arxiv.org/pdf/2210.05639.pdf




if __name__ == '__main__':
    run()
# created on 2023-04-20
# updated on 2023-04-24
