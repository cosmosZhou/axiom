from util import *


@apply
def apply(ne_zero, eq, Q_pi_def, V_pi_def):
    args = ne_zero.of(Unequal[Probability[Equal & Equal], 0])
    if isinstance(ne_zero.of(Unequal[Probability[Equal & Equal], 0])[-1], Tuple):
        args, *weights = args
    else:
        weights = []

    (a, S[a.var]), (s, S[s.var]) = args
        
    if weights:
        (S[a], θ), = weights

    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    (((Gt, ((S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), *S[weights])), V_pi_st_var = V_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal]]])
    ((γ, k), (r, (S[k], S[t]))), (S[k], S[0], S[oo]) = Gt
    (((S[Gt], ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), *S[weights])), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random

    if weights:
        S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
        S[s[t].var], [S[θ]] = V_pi_st_var.of(Function)
        limits_Q = [(a[t], θ)]
        limits_V = [(r[t + 1],), (s[t + 1],), *weights]
    else:
        S[s[t].var], S[a[t].var] = Q_pi_st_var.of(Function)
        S[s[t].var] = V_pi_st_var.of(Function)
        limits_Q = limits_V = []
    
    V_pi_st = V_pi_st_var._subs(s[t].var, s[t + 1])
    return Equal(V_pi_st_var, Expectation(Q_pi_st_var._subs(a[t].var, a[t]) | s[t], *limits_Q)),\
        Equal(V_pi_st_var, Expectation((r[t + 1] + γ * V_pi_st) | s[t], *limits_V)), \
        Equal(Q_pi_st_var, Expectation((r[t + 1] + γ * V_pi_st) | s[t] & a[t], *limits_V))


@prove
def prove(Eq):
    from axiom import keras, algebra, stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time step counter
    V_pi = Function(r'V^\pi', real=True, shape=()) #Value Function
    Q_pi = Function(r'Q^\pi', real=True, shape=()) #Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    G = Lamda[t](Sum[k:0:oo](γ ** k * r[t + k + 1])) #sum of discounted future reward
    Eq << apply(Unequal(Probability(s, a), 0),
                Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption
                Equal(Q_pi(s[t].var, a[t].var), Expectation(G[t] | s[t] & a[t])),
                Equal(V_pi(s[t].var), Expectation(G[t] | s[t])))

    Eq << keras.ne_zero.eq.imply.eq.V_function.apply(Eq[0], Eq[2])

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[3], Eq[-1])

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[0])[1]

    Eq << stats.eq.imply.eq.single_condition.apply(Eq[1], s[t])

    Eq << keras.ne_zero.eq.imply.eq.Bellman.apply(Eq[-2], Eq[-1], γ, k)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[3], Eq[-1])

    Eq << Eq[3].subs(t, t + 1)

    Eq.v_next = Eq[-1].subs(s[t + 1].var, s[t + 1])

    Eq << Eq[-2].subs(Eq.v_next.reversed)

    Eq << keras.ne_zero.eq.imply.eq.Bellman.conditioned.apply(Eq[0], Eq[1], γ, k)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[2], Eq[-1])

    Eq << Eq[-1].subs(Eq.v_next.reversed)

    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#bellman-equations
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    #https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#id4
    #https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    #https://www.youtube.com/watch?v=cQfOQcpYRzE
    #https://www.52coding.com.cn/tags/Reinforcement-Learning/
    #TRPO
    #https://arxiv.org/pdf/1502.05477.pdf
    
    


if __name__ == '__main__':
    run()
# created on 2023-03-28
# updated on 2023-03-29
