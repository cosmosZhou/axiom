from util import *


@apply
def apply(ne_zero, eq, eq_markov_1st, Q_pi_def, V_pi_def, pi_def, lt, n=None, a_quote=None, s_quote=None):
    ((a, S[a.var]), (s, S[s.var])), (S[a], θ) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])    
    ((S[s], t), S[s[:t].as_boolean()]), (S[s[t]], S[s[t - 1].as_boolean()]) = eq_markov_1st.of(Equal[Conditioned[Indexed], Conditioned])
    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    (((Gt, ((S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), V_pi_st_var = V_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal]]])
    ((γ, k), (S[r], (S[k], S[t]))), (S[k], S[0], S[oo]) = Gt
    (((S[Gt], ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random

    S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
    S[s[t].var], [S[θ]] = V_pi_st_var.of(Function)
    
    (S[a[t].as_boolean() | s[t]], [S[a], S[θ]]), pi_st_var = pi_def.of(Equal[Probability])
    def pi_theta(a_, s_):
        return pi_st_var._subs(a[t].var, a_)._subs(s[t].var, s_)
    
    S[Derivative[θ](V_pi_st_var._subs(s[t].var, s[n])) | s[0]], [S[s[n]]] = lt.of(Abs[Expectation] < Infinity)
    return Equal(Derivative[θ](V_pi_st_var._subs(s[t].var, s[0].var)),
                 Sum[a_quote](Derivative[θ](pi_theta(a_quote, s[0].var)) * Q_pi_st_var._subs(s[t].var, s[0].var)._subs(a[t].var, a_quote)) + \
                 Sum[s_quote](Sum[k:1:oo](γ ** k * Probability(Equal(s[k], s_quote) | s[0])) * Sum[a_quote](Derivative[θ](pi_theta(a_quote, s_quote)) * Q_pi_st_var._subs(s[t].var, s_quote)._subs(a[t].var, a_quote))))


@prove
def prove(Eq):
    from axiom import keras, calculus, algebra
    
    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), integer=True, random=True) #states / observation
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
    pi = Function(real=True, shape=())
    a_quote = Symbol(integer=True)
    s_quote = Symbol(shape=(b,), integer=True)
    *Eq[-7:], Eq.hypothesis = apply(Unequal(Probability[a:θ](s, a), 0),
                Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption for rewards bases on states and actions
                Equal(s[t] | s[:t], s[t] | s[t - 1]), #first order markov assumption of states
                Equal(Q_pi[θ](s[t].var, a[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t] & a[t])),
                Equal(V_pi[θ](s[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t])),
                Equal(Probability[a:θ](a[t] | s[t]), pi[θ](a[t].var, s[t].var)),
                Less(Abs(Expectation(Derivative[θ](V_pi[θ](s[n])) | s[0])), oo, evaluate=False),
                n, a_quote, s_quote)
    
    Eq << keras.ne_zero.eq.eq.eq.eq.imply.eq.policy_gradient.induct.discrete.apply(*Eq[:5], n)
    
    Eq << Eq[5].subs(t, 0)
    
    Eq << Eq[-2].subs(Eq[-1])
    
    Eq << Eq[5].subs(t, k)
    
    Eq << Eq[-1].subs(a[k].var, a[t].var)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].this.find(Sum).limits_subs(a[0].var, a_quote)
    
    Eq << Eq[-1].this.find(Sum[2]).limits_subs(s[k].var, s_quote)
    
    Eq << calculus.eq.imply.eq.limit.apply(Eq[-1], (n, oo))
    
    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.add)
    
    Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)
    
    Eq << Eq[-1].this.lhs.doit()
    
    Eq << calculus.lt.is_finite.imply.is_zero.limit.apply(Eq[-1], Eq[6], n)
    
    Eq << Eq[-3].subs(Eq[-1])
    
    Eq << Eq[-1].this.find(Limit).apply(calculus.limit.to.sum)
    
    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.limits.swap)
    
    Eq << Eq[-1].this.find(Sum[Mul[~Sum]]).limits_subs(a[t].var, a_quote)
    
    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.limits.separate)
    
    
    
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
