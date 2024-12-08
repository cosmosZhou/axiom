from util import *


@apply
def apply(eq, V_def, lt_dV, lt_V):
    from Axiom.Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, V_st_var = extract_QVA(eq, None, V_def, None, lt_dV)

    S[V_st_var], [S[s[t].var]], [S[t]] = lt_V.of(Sup[Abs] < Infinity)

    At = γ ** Lamda[t](t) @ (r[t:] + γ * V_st_var._subs(s[t].var, s[t + 1:]) - V_st_var._subs(s[t].var, s[t:]))
    return Equal(γ ** Lamda[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Lamda[t](t) @ Lamda[t](Expectation[r, a:π, s](Derivative[π](log(Probability[a:π](a[t].surrogate | s[t].surrogate))) * At)))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Calculus, Stats, Keras

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V = Function(real=True, shape=property(lambda self: self.arg.shape[:-1])) # State-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-4:], Eq.hypothesis = apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Less(Sup[s[t].var, t](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo),
                Less(Sup[s[t].var, t](Abs((V[π] ^ γ)(s[t].var))), oo))

    Eq.eq_matmul = Eq.hypothesis.find(Expectation, MatMul)._subs(s, s.var)._subs(r, r.var).this.apply(Discrete.Dot.eq.Sum)

    k = Symbol(integer=True) # time step counter
    Eq << Eq.eq_matmul.rhs._subs(oo, k).this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.rhs.find(Symbol * Pow).args[:2].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.rhs(t).find(Max).simplify()

    Eq << Calculus.Eq.to.Eq.Limit.apply(Eq[-1], (k, oo))

    Eq << Eq[-1].this.lhs.apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.rhs.find(Limit).apply(Calculus.Limit.eq.Add)

    Eq.limit = Eq[-1].this.find(Limit[Sum]).apply(Calculus.Limit.eq.Sum)

    Eq << Algebra.All_Le_Sup.apply(Eq[3].lhs)

    Eq << Eq[-1].subs(t, t + k)

    Eq << Algebra.Cond.to.All.apply(Eq[-1], k, simplify=None)

    Eq << Algebra.All_Le.to.LeSup.apply(Eq[-1])

    Eq << Algebra.Le.Lt.to.Lt.trans.apply(Eq[-1], Eq[3])

    Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Calculus.LtAbs.is_finite.to.Eq_0.Limit.apply(Eq[-2], Eq[-1])

    Eq << Eq.limit.subs(Eq[-1])

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.eq_matmul, Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.eq.Dot)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(Algebra.Lamda.eq.Pow)

    Eq << Eq[-1].this.rhs.find(Lamda).limits_subs(Eq[-1].rhs.find(Lamda).variable, t)

    Eq << Eq[-1].subs(s.var, s).subs(r.var, r)

    Eq << Eq.hypothesis.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Add]).apply(Stats.Expect.eq.Add)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Stats.Expect.eq.Mul)

    Eq << Eq[-1].find(-~Expectation).this.apply(Stats.Expect.law_of_iterated_expectation, s[t])

    Eq << Eq[-1].this.find(Expectation[~Expectation]).apply(Stats.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Mul[~Expectation]).apply(Stats.Expect.Conditioned.eq.Zero.st.Grad.Log.Prob)

    Eq << Eq[-4].subs(Eq[-1])

    Eq << Eq[2].subs(Eq[1])

    Eq << Eq[-1].this.find(Derivative).apply(Calculus.Grad.Dot.eq.Dot.Grad)

    Eq << Keras.Eq_Conditioned.is_finite.to.Eq.Dot.Grad.Expect.policy_gradient_theorem.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation).simplify()

    # https://arxiv.org/pdf/1506.02438.pdf#page=4




if __name__ == '__main__':
    run()
# created on 2023-04-13
# updated on 2023-05-20
