from util import *


@apply
def apply(eq, Q_def, V_def, lt):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def, None, lt)
    return Equal(γ ** Lamda[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Lamda[t](t) @ Lamda[t](Expectation[a:π, s](Derivative[π](log(Probability[a:π](a[t].surrogate | s[t].surrogate))) * Q_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t]))))


@prove
def prove(Eq):
    from axiom import keras, calculus, stats, algebra, discrete

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    π = Symbol(shape=(D,), real=True) #trainable weights for the agent
    t = Symbol(integer=True) #time step counter
    V, Q = Function(real=True, shape=()) #State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-4:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Less(Sup[s[t].var, t](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo))

    n = Symbol(integer=True, nonnegative=True)
    Eq.expect = keras.eq_conditioned.eq_expect.eq_expect.imply.eq.grad.expect.policy_gradient.apply(*Eq[:3], n)

    Eq << calculus.eq.imply.eq.limit.apply(Eq.expect, (n, oo))

    Eq.limit = Eq[-1].this.find(Limit).apply(calculus.limit.to.add)

    Eq << stats.imply.abs_le.expect.abs.apply(Eq.limit.find(Expectation[Derivative]).subs(n, t))

    Eq << stats.imply.expect_le.sup.apply(Eq[-1].rhs)

    Eq.le_sup = algebra.le.le.imply.le.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.imply.all.le_sup.apply(Eq[3].lhs)

    Eq << algebra.cond.imply.all.apply(Eq[-1], s[t].var, simplify=None)

    Eq << algebra.all_le.imply.sup_le.apply(Eq[-1])

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-1], Eq.le_sup)

    Eq << algebra.cond.imply.all.apply(Eq[-1], t, simplify=None)

    Eq << algebra.all_le.imply.sup_le.apply(Eq[-1])

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[3], Eq[-1])

    Eq << Eq[-1].this.lhs.limits_subs(t, n)

    Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq[-1].this.lhs.doit()

    Eq << calculus.abs_lt.is_finite.imply.is_zero.limit.apply(Eq[-2], Eq[-1])

    Eq << Eq.limit.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation[Sum]).apply(stats.expect.sum.to.sum.expect)

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.sum)

    Eq << Eq[-1].this.rhs.apply(stats.sum.expect.to.expect.sum)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul, 1)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.matmul)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.lamda.to.lamda.expect)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(algebra.lamda.to.pow)

    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#bellman-equations
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    #https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    #https://danieltakeshi.github.io/2017/04/02/notes-on-the-generalized-advantage-estimation-paper/
    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#id4
    #https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    #https://www.52coding.com.cn/tags/Reinforcement-Learning/
    #TRPO
    #https://arxiv.org/pdf/1502.05477.pdf




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-04-14
