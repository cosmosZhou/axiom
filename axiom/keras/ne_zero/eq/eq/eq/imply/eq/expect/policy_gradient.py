from util import *


@apply
def apply(ne_zero, eq, Q_pi_def, V_pi_def, n=None):
    ((a, S[a.var]), (s, S[s.var])), (S[a], θ) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])
    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    (((Gt, ((S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), V_pi_st_var = V_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal]]])
    ((γ, k), (S[r], (S[k], S[t]))), (S[k], S[0], S[oo]) = Gt
    (((S[Gt], ((S[a[t]], S[a[t].var]), (S[s[t]], S[s[t].var]))), (S[r[t + 1:]],), (S[a], S[θ]))), Q_pi_st_var = Q_pi_def.of(Equal[Expectation[Conditioned[Sum[Symbol ** Symbol * Indexed[Symbol, Symbol + Symbol + 1]], Equal & Equal]]])
    assert a.is_random and s.is_random and r.is_random

    S[s[t].var], S[a[t].var], [S[θ]] = Q_pi_st_var.of(Function)
    S[s[t].var], [S[θ]] = V_pi_st_var.of(Function)
    assert n >= 0
    return Equal(Derivative[θ](Expectation[r[1:], a:θ](Sum[k:0:oo](γ ** k * r[k + 1]))),
                 Expectation(Sum[k:n](γ ** k * Expectation[a:θ](Derivative[θ](log(Probability[a:θ](a[k].surrogate | s[k].surrogate))) * Q_pi_st_var._subs(s[t].var, s[k])._subs(a[t].var, a[k]) | s[k].surrogate))) + \
                 γ ** n * Expectation(Derivative[θ](V_pi_st_var._subs(s[t].var, s[n]))))




@prove
def prove(Eq):
    from axiom import stats, calculus, keras, algebra

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
    n = Symbol(integer=True, nonnegative=True, given=False)
    *Eq[-4:], Eq.hypothesis = apply(Unequal(Probability[a:θ](s, a), 0),
                Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption for rewards bases on states and actions
                Equal(Q_pi[θ](s[t].var, a[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t] & a[t])),
                Equal(V_pi[θ](s[t].var), Expectation[r[t + 1:], a:θ](G[t] | s[t])), n)

    Eq << Eq[3].subs(t, 0)

    Eq << Eq[-1].subs(s[0].var, s[0])

    Eq << stats.eq.imply.eq.expect.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(stats.expect.law_of_total_expectation)

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], [θ])

    Eq << Eq[-1].this.lhs.apply(stats.grad_expect.to.expect.grad).reversed

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    Eq << keras.ne_zero.eq.eq.eq.imply.eq.policy_gradient.induct.apply(*Eq[:4], n)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.rhs.apply(calculus.integral.to.add)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Integral[Sum]).apply(calculus.integral.to.sum)

    Eq << Eq[-1].this.find(Integral[Mul]).apply(calculus.integral.to.mul)

    Eq << Eq[-1].this.find(Sum[~Integral[Mul]]).apply(calculus.integral.to.mul)

    Eq << Eq[-1].this.find(Integral[~Mul[Integral]]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Integral[~Mul[Integral]]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.concat)

    Eq << Eq[-1].this.find(Sum[Mul[~Integral]]).apply(calculus.integral.limits.concat)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.split.slice.pop)

    Eq << Eq[-1].this.rhs.find(Sum)().find(Integral).apply(calculus.integral.limits.split.slice.pop)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Derivative * ~Integral).apply(stats.integral_prod.to.prob)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.expect)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability * Product]).apply(stats.integral_prod.to.prob)

    Eq << Eq[-1].this.find(Derivative[Probability]).apply(calculus.grad.to.mul.grad.log)

    Eq << Eq[-1].this.find(Probability * ~Sum).apply(stats.sum.to.expect)

    Eq << Eq[-1].this.find(Integral).apply(stats.integral.to.expect)

    Eq << Eq[-1].this.find(Mul[Expectation[Expectation]]).apply(stats.mul.to.expect)

    Eq << Eq[-1].this.find(Sum[Expectation]).apply(stats.sum_expect.to.expect.sum)

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
# created on 2023-04-04
