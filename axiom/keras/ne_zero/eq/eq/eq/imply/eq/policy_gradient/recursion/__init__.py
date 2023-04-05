from util import *


@apply
def apply(ne_zero, eq, Q_pi_def, V_pi_def):
    ((a, S[a.var]), (s, S[s.var])), (S[a], θ) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])
    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    (((Gt, ((S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), V_pi_st_var = V_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal]]])
    ((γ, k), (S[r], (S[k], S[t]))), (S[k], S[0], S[oo]) = Gt
    (((S[Gt], ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random

    S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
    S[s[t].var], [S[θ]] = V_pi_st_var.of(Function)

    return Equal(Derivative[θ](V_pi_st_var),
                 Sum[a[t].var](Derivative[θ](Probability[a:θ](a[t] | s[t])) * Q_pi_st_var) + \
                 γ * Integral[s[t + 1].var](Derivative[θ](V_pi_st_var._subs(t, t + 1)) * Probability(s[t + 1] | s[t])))


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
    Eq << apply(Unequal(Probability[a:θ](s, a), 0),
                Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption
                Equal(Q_pi[θ](s[t].var, a[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t] & a[t])),
                Equal(V_pi[θ](s[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t])))

    Eq << keras.ne_zero.eq.eq.eq.imply.et.eq.Bellman.apply(*Eq[:4])

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], [θ])

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(calculus.sum.to.integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.add)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability]).apply(stats.integral.to.prob)

    Eq << calculus.eq.imply.eq.grad.apply(Eq[5], [θ])

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.sum)

    Eq << Eq[-1].subs(Eq[-4])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Derivative[Integral]).apply(calculus.grad.to.integral)

    Eq << Eq[-1].this.find(Probability * Integral).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Sum[Integral]).apply(calculus.sum.to.integral)

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[0], (t, t))
    Eq << stats.ne_zero.imply.eq.bayes.conditioned.st.joint.apply(Eq[-1], s[t + 1], a[t])
    Eq << Eq[-3].subs(Eq[-1].reversed)
    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)
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
del discrete
from . import discrete
