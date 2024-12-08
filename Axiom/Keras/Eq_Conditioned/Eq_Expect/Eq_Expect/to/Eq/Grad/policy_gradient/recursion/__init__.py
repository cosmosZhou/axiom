from util import *


@apply
def apply(eq, Q_def, V_def):
    from Axiom.Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    return Equal(Derivative[π](V_st_var),
                 Sum[a[t].var](Derivative[π](Probability[a:π](a[t] | s[t])) * Q_st_var) + \
                 γ * Integral[s[t + 1].var](Derivative[π](V_st_var._subs(t, t + 1)) * Probability(s[t + 1] | s[t])))


@prove
def prove(Eq):
    from Axiom import Keras, Calculus, Stats, Algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])))

    Eq << Keras.Eq_Conditioned.Eq_Expect.Eq_Expect.to.And.Eq.Expect.Bellman.apply(*Eq[:3])

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq[-1], [π])

    Eq << Eq[-1].this.find(Expectation).apply(Stats.Expect.eq.Sum)

    Eq << Eq[-1].this.find(Sum).apply(Calculus.Sum.eq.Integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(Stats.Sum.eq.Prob)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability]).apply(Stats.Integral.eq.Prob.marginal)

    Eq << Calculus.Eq.to.Eq.Grad.apply(Eq[4], [π])

    Eq << Eq[-1].this.find(Expectation).apply(Stats.Expect.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Sum)

    Eq << Eq[-1].subs(Eq[-4])

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.find(Derivative[Integral]).apply(Calculus.Grad.eq.Integral)

    Eq << Eq[-1].this.find(Probability * Integral).apply(Calculus.Mul.eq.Integral)

    Eq.eq_grad = Eq[-1].this.find(Sum[Integral]).apply(Calculus.Sum.eq.Integral)

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0]).subs(t, t + 1)

    Eq << Stats.Ne_0.to.Ne_0.joint_slice.apply(Eq[-1], [-1, -1])

    Eq << Stats.Cond.to.Cond.Prob.weighted.apply(Eq[-1], (a, π))

    Eq << Stats.Ne_0.to.Eq.Prob.Conditioned.eq.Mul.Prob.Conditioned.bayes.apply(Eq[-1], s[t + 1], a[t])

    Eq << Eq.eq_grad.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(Stats.Sum.eq.Prob)
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# bellman-equations
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    # https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    # https://danieltakeshi.github.io/2017/04/02/notes-on-the-generalized-advantage-estimation-paper/
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# id4
    # https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    # https://www.52coding.com.cn/tags/Reinforcement-Learning/
    # TRPO
    # https://arxiv.org/pdf/1502.05477.pdf




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-04-29


del discrete
from . import discrete
