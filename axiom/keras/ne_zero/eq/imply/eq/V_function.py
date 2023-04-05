from util import *


@apply
def apply(ne_zero, Q_pi_def):
    (a, S[a.var]), (s, S[s.var]) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])

    (((((γ, k), (r, (S[k], t))), (S[k], S[0], S[oo])), ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), [S[r[t + 1:]]]), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Add[One]]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random
    weights = []
    if weights:
        S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
    else:
        S[s[t].var], S[a[t].var] = Q_pi_st_var.of(Function)
        
    return Equal(Expectation(Sum[k:0:oo](γ ** k * r[t + k + 1]) | s[t]), Expectation(Q_pi_st_var._subs(a[t].var, a[t]) | s[t]))


@prove
def prove(Eq):
    from axiom import stats, calculus

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time countor
    Q_pi = Function(r'Q^\pi', real=True, shape=()) #Action-Value Function
    γ = Symbol(domain=Interval(0, 1, left_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    G = Lamda[t](Sum[k:0:oo](γ ** k * r[t + k + 1])) #sum of discounted future reward
    Eq << apply(Unequal(Probability(s, a), 0),
                Equal(Q_pi(s[t].var, a[t].var), Expectation(G[t] | s[t] & a[t])))

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.sum)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[0], (t, t))

    Eq << stats.ne_zero.imply.eq.bayes.conditioned.st.joint.apply(Eq[-1], a[t], r[t + 1:])

    Eq << Eq[-3].subs(Eq[-1].reversed)
    
    Eq << Eq[-1].this.rhs.apply(calculus.sum.to.integral)
    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)
    Eq << Eq[-1].this.lhs.apply(stats.expect.to.integral)
    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#bellman-equations
    #https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf
    #https://spinningup.openai.com/en/latest/spinningup/rl_intro.html#id4
    #https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    #https://www.youtube.com/watch?v=cQfOQcpYRzE
    #https://www.52coding.com.cn/tags/Reinforcement-Learning/
    #TRPO
    #https://arxiv.org/pdf/1502.05477.pdf
    


if __name__ == '__main__':
    run()
# created on 2023-03-29
