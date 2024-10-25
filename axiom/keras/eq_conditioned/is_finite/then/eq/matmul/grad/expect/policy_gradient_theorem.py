from util import *


@apply
def apply(eq, lt):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    assert a.is_random and s.is_random and r.is_random

    ((γ, (S[t], [S[t]])), (((S[r[t:]], S[s[t].as_boolean()]), (S[r[t:]],), (S[a], π)), [S[π], S[1]])), [S[s[t].var]], [S[t]] = lt.of(Sup[Abs[Pow[Lamda] @ Derivative[Expectation[Conditioned]]]] < Infinity)
    return Equal(γ ** Lamda[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Lamda[t](t) @ Lamda[t](Expectation[r, a:π, s](Derivative[π](log(Probability[a:π](a[t].surrogate | s[t].surrogate))) * (γ ** Lamda[t](t) @ r[t:]))))


@prove
def prove(Eq):
    from axiom import calculus, keras, discrete, stats, algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation

    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-2:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Less(Sup[s[t].var, t](Abs(γ ** Lamda[t](t) @ Derivative[π](Expectation[r[t:], a:π](r[t:] | s[t])))), oo))

    @Function(real=True, shape=())# Action-Value Function
    def Q(st, at, *limits):
        [π], [γ] = limits
        s_var, t = st.of(Indexed)
        a_var, S[t] = at.of(Indexed)
        assert s[t] != st and a[t] != at
        return γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | Equal(s[t], st) & Equal(a[t], at))
    Eq.Q_Function = (Q[π] ^ γ)(s[t].var, a[t].var).this.defun()

    @Function(real=True, shape=())# State-Value Function
    def V(st, *limits):
        [π], [γ] = limits
        s_var, t = st.of(Indexed)
        assert s[t] != st
        return γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | Equal(s[t], st))
    Eq.V_Function = (V[π] ^ γ)(s[t].var).this.defun()

    Eq << Eq[1].this.find(MatMul).apply(calculus.matmul.grad.to.grad.matmul)

    Eq << Eq[-1].subs(Eq.V_Function.reversed)

    Eq << keras.eq_conditioned.eq_expect.eq_expect.is_finite.then.eq.matmul.grad.expect.Q_Function.apply(Eq[0], Eq.Q_Function, Eq.V_Function, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Mul[Expectation]).apply(stats.mul.to.expect)

    Eq.eq_expect = Eq[-1].this.rhs.apply(stats.sum.expect.to.expect.sum)

    Eq << keras.eq_conditioned.then.eq.expect.grad.log.prob.Q_Function.discounted.apply(Eq[0], γ, t, π)

    Eq << Eq.Q_Function.subs(s[t].var, s[t]).subs(a[t].var, a[t])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1] * γ ** t

    Eq << Eq[-1].this.lhs.apply(stats.mul.to.expect)

    Eq << Eq[-1].this.rhs.apply(stats.mul.to.expect)

    Eq << algebra.eq.then.eq.sum.apply(Eq[-1], (t, 0, oo))

    Eq << Eq[-1].this.rhs.apply(stats.sum.expect.to.expect.sum)

    Eq << Eq[-1].this.lhs.apply(stats.sum.expect.to.expect.sum)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq.eq_expect, Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul, 1)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.matmul)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.pow)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.lamda.to.lamda.expect)

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
# created on 2023-04-07
# updated on 2023-04-14
