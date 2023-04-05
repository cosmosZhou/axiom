from util import *


@apply
def apply(ne_zero, eq, Q_pi_def, V_pi_def, lt, n=None):
    ((a, S[a.var]), (s, S[s.var])), (S[a], θ) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])
    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    (((Gt, ((S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), V_pi_st_var = V_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal]]])
    ((γ, k), (S[r], (S[k], S[t]))), (S[k], S[0], S[oo]) = Gt
    (((S[Gt], ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random

    S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
    S[s[t].var], [S[θ]] = V_pi_st_var.of(Function)

    S[Derivative[θ](V_pi_st_var)], (S[s[t].var],) = lt.of(Sup[Abs] < Infinity)
    return Equal(Derivative[θ](Expectation[r[1:], a:θ](Sum[k:0:oo](γ ** k * r[k + 1]))),
                 Expectation(Sum[k](γ ** k * Expectation[a:θ](Derivative[θ](log(Probability[a:θ](a[k].surrogate | s[k].surrogate))) * (Q_pi_st_var._subs(s[t].var, s[k])._subs(a[t].var, a[k])) | s[k].surrogate))))


@prove
def prove(Eq):
    from axiom import keras, calculus, stats, algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    #A = Symbol(etype=dtype.integer) #the set of actions to taken for the agent
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    θ = Symbol(shape=(D,), real=True) #trainable weights for the agent
    t, k = Symbol(integer=True) #time step counter
    V_pi = Function(r'V^\pi', real=True, shape=()) #Value Function
    Q_pi = Function(r'Q^\pi', real=True, shape=()) #Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    G = Lamda[t](Sum[k:0:oo](γ ** k * r[t + k + 1])) #sum of discounted future reward
    n = Symbol(integer=True, positive=True, given=False)
    *Eq[-5:], Eq.hypothesis = apply(Unequal(Probability[a:θ](s, a), 0),
                Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption for rewards bases on states and actions
                Equal(Q_pi[θ](s[t].var, a[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t] & a[t])),
                Equal(V_pi[θ](s[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t])),
                Less(Sup[s[t].var](Abs(Derivative[θ](V_pi[θ](s[t].var)))), oo, evaluate=False),
                n)

    Eq.expect = keras.ne_zero.eq.eq.eq.imply.eq.expect.policy_gradient.apply(*Eq[:4], n)

    Eq << calculus.eq.imply.eq.limit.apply(Eq.expect, (n, oo))

    Eq.limit = Eq[-1].this.find(Limit).apply(calculus.limit.to.add)

    Eq << stats.imply.abs_le.expect_abs.apply(Eq.limit.find(Expectation[Derivative]))

    Eq << stats.imply.expect_le.sup.apply(Eq[-1].rhs)

    Eq << algebra.le.le.imply.le.transit.apply(Eq[-2], Eq[-1])

    Eq << algebra.le.lt.imply.lt.transit.apply(Eq[-1], Eq[4].subs(t, n))

    Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq[-1].this.lhs.doit()

    Eq << calculus.lt.is_finite.imply.is_zero.limit.apply(Eq[-2], Eq[-1], n)

    Eq << Eq.limit.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation[Sum]).apply(stats.expect_sum.to.sum.expect)

    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.sum)

    Eq << Eq[-1].this.rhs.apply(stats.sum_expect.to.expect.sum)

    
    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#bellman-equations
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    #https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    #https://danieltakeshi.github.io/2017/04/02/notes-on-the-generalized-advantage-estimation-paper/
    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#id4
    #https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    #https://www.youtube.com/watch?v=cQfOQcpYRzE
    #https://www.52coding.com.cn/tags/Reinforcement-Learning/
    #TRPO
    #https://arxiv.org/pdf/1502.05477.pdf
    
    


if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-04-04
