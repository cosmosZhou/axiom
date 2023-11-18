from util import *


@apply
def apply(eq, Q_def, V_def, A_def, lt):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var, A_st_var = extract_QVA(eq, Q_def, V_def, A_def, lt)
    return Equal(γ ** Lamda[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Lamda[t](t) @ Lamda[t](Expectation[a:π, s](Derivative[π](log(Probability[a:π](a[t].surrogate | s[t].surrogate))) * A_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t]))))


@prove
def prove(Eq):
    from axiom import keras, algebra, stats

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation

    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    π = Symbol(shape=(D,), real=True) #trainable weights for the agent
    t = Symbol(integer=True) #time step counter
    V, Q, A = Function(real=True, shape=()) #State-Value, Action-Value, Advantage Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-5:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((A[π] ^ γ)(s[t].var, a[t].var), (Q[π] ^ γ)(s[t].var, a[t].var) - (V[π] ^ γ)(s[t].var)),
                Less(Sup[s[t].var, t](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo))

    Eq << keras.eq_conditioned.eq_expect.eq_expect.is_finite.imply.eq.matmul.grad.expect.Q_Function.apply(*Eq[:3], Eq[4])

    Eq << Eq[-1].this.rhs.find(Expectation).simplify()

    Eq.hypothesis = Eq.hypothesis.subs(Eq[3].subs(s[t].var, s[t]).subs(a[t].var, a[t]))

    Eq << Eq.hypothesis.this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.to.add)

    Eq.hypothesis = Eq[-1].this.find(Expectation[Mul[NegativeOne]]).apply(stats.expect.to.mul)

    Eq << Eq.hypothesis.rhs.find(-~Expectation).this.apply(stats.expect.law_of_iterated_expectation, s[t])

    Eq << Eq[-1].this.find(Expectation[~Expectation]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Mul[~Expectation]).apply(stats.expect.conditioned.to.zero.st.grad.log.prob)

    Eq << Eq.hypothesis.subs(Eq[-1])

    #https://arxiv.org/pdf/1506.02438.pdf#page=13 (Proof of Proposition 1)




if __name__ == '__main__':
    run()
# created on 2023-04-13


# updated on 2023-04-14
from . import importance_sampling
