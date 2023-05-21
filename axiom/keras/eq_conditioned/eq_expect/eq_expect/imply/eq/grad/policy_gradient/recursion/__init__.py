from util import *


@apply
def apply(eq, Q_def, V_def):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    return Equal(Derivative[π](V_st_var),
                 Sum[a[t].var](Derivative[π](Probability[a:π](a[t] | s[t])) * Q_st_var) + \
                 γ * Integral[s[t + 1].var](Derivative[π](V_st_var._subs(t, t + 1)) * Probability(s[t + 1] | s[t])))


@prove
def prove(Eq):
    from axiom import keras, calculus, stats, algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    π = Symbol(shape=(D,), real=True) #trainable weights for the agent
    t = Symbol(integer=True) #time step counter
    V, Q = Function(real=True, shape=()) #State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])))

    Eq << keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman.apply(*Eq[:3])

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], [π])

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(calculus.sum.to.integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.to.add)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.add)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Probability]).apply(stats.integral.to.prob.marginal)

    Eq << calculus.eq.imply.eq.grad.apply(Eq[4], [π])

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.rhs.apply(calculus.grad.to.sum)

    Eq << Eq[-1].subs(Eq[-4])

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Derivative[Integral]).apply(calculus.grad.to.integral)

    Eq << Eq[-1].this.find(Probability * Integral).apply(calculus.mul.to.integral)

    Eq.eq_grad = Eq[-1].this.find(Sum[Integral]).apply(calculus.sum.to.integral)

    

    
    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0]).subs(t, t + 1)
    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[-1], [-1, -1])
    Eq << stats.cond.imply.cond.prob.weighted.apply(Eq[-1], (a, π))
    Eq << stats.ne_zero.imply.eq.bayes.conditioned.st.joint.apply(Eq[-1], s[t + 1], a[t])
    Eq << Eq.eq_grad.subs(Eq[-1].reversed)
    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)
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
del discrete
# updated on 2023-04-29
from . import discrete
