from util import *


@apply
def apply(eq, Q_def, V_def, MDV_def, any, eq_argmax):
    from Axiom.Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    (((S[Q_st_var._subs(a[t].var, a[t])], S[s[t].as_boolean()]), (a, π_quote)), ((S[Probability[a:π_quote](a[t] | s[t])], S[Probability[a:π](a[t] | s[t])]), S[Probability[π, π_quote](s[t])], S[Probability[s:π](s[t])])), MDV_st_var = MDV_def.of(Equal[Expectation[Conditioned] - KL * Expr / Expr])
    ((S[MDV_st_var._subs(s[t].var, s[t])._subs(t, 0)], (s, π)), [S[π_quote]]), π_tilde = eq_argmax.of(Equal[ArgMax[Expectation]])

    return V_st_var._subs(π, π_tilde) >= V_st_var, \
        γ ** Lamda[t](t) @ Expectation[r, a:π_tilde](r) >= γ ** Lamda[t](t) @ Expectation[r, a:π](r)


@prove
def prove(Eq):
    from Axiom import Algebra, Stats, Sets

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), integer=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True) # time step counter
    π = Symbol(shape=(D,), real=True, given=True) # trainable weights for the agent
    π_quote = Symbol(shape=(D,), real=True)
    π_hat = Symbol(r'\hat{π}', shape=(D,), real=True)
    π_tilde = Symbol(r"\tilde{π}", shape=(D,), real=True, given=True) # optimal weights for the new policy
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True), given=True) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    MDV = Function(r'\mathcal{M}_\mathfrak{D}V', real=True, shape=())
    *Eq[-6:], (Eq.ge_VF, Eq.ge_reward) = apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((MDV[π, π_quote] ^ γ)(s[t].var), Expectation[a:π_quote]((Q[π] ^ γ)(s[t].var, a[t]) | s[t]) - Probability[π, π_quote](s[t]) / Probability[s:π](s[t]) * KL(Probability[a:π_quote](a[t] | s[t]), Probability[a:π](a[t] | s[t]))),
                Exists[π_hat](And(
                    Equal(Probability[a:π_hat](a[0] | s[0]), Piecewise((Probability[a:π](a[0] | s[0]), Equal(s[0].var, s[t].var)), (Probability[a:π_quote](a[0] | s[0]), True))),
                    Equal(Probability[π, π_hat](s[0]), Piecewise((Probability[π, π](s[0]), Equal(s[0].var, s[t].var)), (Probability[π, π_quote](s[0]), True))))),
                Equal(π_tilde, ArgMax[π_quote](Expectation[s:π]((MDV[π, π_quote] ^ γ)(s[0])))))

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[3])

    Eq.ne_zero = Eq[-1].subs(t, 0)

    Eq << Algebra.Eq_ArgMax.to.All.Ge.apply(Eq[5])

    Eq << Eq[-1].subs(π_quote, π_hat)

    Eq << Algebra.Ge.to.Ge_0.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Stats.Add.Expect.eq.Expect)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.apply(Stats.Expect.eq.Sum)

    Eq.ge_sum = Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.split, cond={s[t].var})

    Eq.infer = Imply(
        And(Equal(Probability[a:π_hat](a[0] | s[0]), Probability[a:π_tilde](a[0] | s[0])), Equal(Probability[π, π_hat](s[0]), Probability[π, π_tilde](s[0]))),
        Equal((MDV[π, π_tilde] ^ γ)(s[0].var) - (MDV[π, π_hat] ^ γ)(s[0].var), 0),
        plausible=True)

    Eq << Eq[3].subs(t, 0)

    Eq <<= Eq[-1].subs(π_quote, π_tilde), Eq[-1].subs(π_quote, π_hat), Eq[-1].subs(π_quote, π)

    Eq.MDV_pi_tilde, Eq.MDV_pi_hat, Eq.MDV_pi = Eq[-3].this.find(Expectation).apply(Stats.Expect.eq.Sum), Eq[-2].this.find(Expectation).apply(Stats.Expect.eq.Sum), Eq[-1].this.find(Expectation).apply(Stats.Expect.eq.Sum)

    Eq << Eq.infer.subs(Eq.MDV_pi_tilde, Eq.MDV_pi_hat)

    Eq << Algebra.And.of.And.apply(Eq[-1], slice(None, 2))

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1], 0)

    Eq << Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1], 1)

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq << Eq[4].this.find(Equal[Piecewise]).apply(Algebra.Cond_Piece.to.And.Imply)

    Eq << Eq[-1].this.find(Equal[Piecewise]).apply(Algebra.Cond_Piece.to.And.Imply)

    Eq << Eq[-1].this.expr.apply(Algebra.And.to.And.delete, 1)

    Eq << Eq[-1].this.expr.args[1:].apply(Algebra.Imply.Imply.to.Imply.And)

    Eq << Eq[-1].subs(π_quote, π_tilde)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq.infer)

    Eq.any = Eq[-1].this.expr.args[1:].apply(Algebra.Imply.Imply.to.Imply.trans)

    Eq << Eq.ge_sum.this.find(Sum).apply(Algebra.Sum.Bool)

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Complement.equ.And)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << Eq[-1].this.find(Bool).apply(Algebra.Bool.eq.Piece)

    Eq << Eq.any.this.find(Imply[2]).apply(Algebra.Imply.to.Eq.Piece, Eq[-1].find(Piecewise))

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Algebra.And.to.And.apply(Eq.ne_zero)[1].subs(s[0].var, s[t].var)

    Eq << Algebra.Ne_0.to.Gt_0.apply(Eq[-1])

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Gt_0.Ge.to.Ge.Div)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_0.to.Ge)

    Eq.ge_MDV = GreaterEqual((MDV[π, π_tilde] ^ γ)(s[t].var), (MDV[π, π] ^ γ)(s[t].var), plausible=True)

    Eq << ~Eq.ge_MDV

    Eq << Algebra.Any.Any.to.Any.And.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Ge.Lt.to.Lt.trans)

    Eq << Eq[-1].this.find(Imply).apply(Algebra.Imply.to.Imply.subs)

    Eq << Eq[-1].subs(s[0].var, s[t].var)

    Eq << Eq.MDV_pi.subs(s[0].var, s[t].var)

    Eq << Eq.MDV_pi_hat.subs(s[0].var, s[t].var)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(Algebra.Eq.Cond.to.Cond.subs)

    Eq << Eq[3].subs(π_quote, π_tilde)

    Eq << Eq[-1].this.find(Expectation).apply(Stats.Expect.limits.desimp)

    Eq << Stats.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Expect.Ge.to.And.Ge.drift.apply(*Eq[:3], Eq[-1], Eq.ge_MDV)

    # https://arxiv.org/pdf/2201.02373.pdf
    # https://arxiv.org/pdf/2211.11030.pdf
    # https://arxiv.org/pdf/2205.01447.pdf
    # https://arxiv.org/pdf/2210.05639.pdf




if __name__ == '__main__':
    run()
# created on 2023-04-24
# updated on 2023-05-15
