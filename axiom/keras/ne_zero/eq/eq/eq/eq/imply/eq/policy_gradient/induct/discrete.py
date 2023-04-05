from util import *


@apply
def apply(ne_zero, eq, eq_markov_1st, Q_pi_def, V_pi_def, n=None):
    ((a, S[a.var]), (s, S[s.var])), (S[a], θ) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])    
    ((S[s], t), S[s[:t].as_boolean()]), (S[s[t]], S[s[t - 1].as_boolean()]) = eq_markov_1st.of(Equal[Conditioned[Indexed], Conditioned])
    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    (((Gt, ((S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), V_pi_st_var = V_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal]]])
    ((γ, k), (S[r], (S[k], S[t]))), (S[k], S[0], S[oo]) = Gt
    (((S[Gt], ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random

    S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
    S[s[t].var], [S[θ]] = V_pi_st_var.of(Function)
    assert n > 0
    return Equal(Derivative[θ](V_pi_st_var._subs(s[t].var, s[0].var)),
                 Sum[a[0].var](Derivative[θ](Probability[a:θ](a[0] | s[0])) * Q_pi_st_var._subs(s[t].var, s[0].var)._subs(a[t].var, a[0].var)) + \
                 Sum[s[k].var, k:1:n](γ ** k * Probability(s[k] | s[0]) * Sum[a[t].var](Derivative[θ](Probability[a:θ](Equal(a[k], a[t].var) | s[k])) * Q_pi_st_var._subs(s[t].var, s[k].var))) + \
                 γ ** n * Expectation(Derivative[θ](V_pi_st_var._subs(s[t].var, s[n])) | s[0]))


@prove
def prove(Eq):
    from axiom import stats, keras, algebra

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
    *Eq[-5:], Eq.hypothesis = apply(Unequal(Probability[a:θ](s, a), 0),
                Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption for rewards bases on states and actions
                Equal(s[t] | s[:t], s[t] | s[t - 1]), #first order markov assumption of states
                Equal(Q_pi[θ](s[t].var, a[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t] & a[t])),
                Equal(V_pi[θ](s[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t])), n)

    Eq.hypothesis = Eq.hypothesis.this.find(Expectation).apply(stats.expect.to.sum)

    Eq.recursion = keras.ne_zero.eq.eq.eq.imply.eq.policy_gradient.recursion.discrete.apply(Eq[0], Eq[1], Eq[3], Eq[4])

    Eq.initial = Eq.hypothesis.subs(n, 1)

    Eq << Eq.recursion.subs(t, 0)

    Eq.induct = Eq.hypothesis.subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum[2]).apply(algebra.sum.to.add.pop)

    Eq << Eq[-1].this.find(Sum[2]).find(Sum).limits_subs(a[t].var, a[n].var)

    Eq << Eq.recursion.subs(t, n)

    Eq << Eq.hypothesis.subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum[Add]).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Symbol ** Symbol * Symbol).powsimp()

    Eq << Eq[-1].this.find(Probability * Sum[Mul[Probability]]).apply(algebra.mul.to.sum)

    Eq << stats.eq.imply.eq.mul.markov.first_order.apply(Eq[2]).subs(t, n)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum[Derivative * Probability]).apply(algebra.sum.limits.concat)

    Eq << Eq[-1].this.find(Sum[Derivative * Probability]).apply(algebra.sum.limits.split.slice.pop)

    Eq << Eq[-1].this.find(Sum[Derivative * Probability]).apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq.initial, Eq[-1], n=n, start=1)

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
