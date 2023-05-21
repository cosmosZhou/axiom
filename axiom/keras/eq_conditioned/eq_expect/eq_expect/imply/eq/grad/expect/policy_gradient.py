from util import *


@apply
def apply(eq, Q_def, V_def, n=None):
    from axiom.keras.eq_conditioned.eq_expect.eq_expect.imply.et.eq.expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    assert n >= 0
    return Equal(γ ** Lamda[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 Expectation[a:π, s[:n]](Sum[t:n](γ ** t * Derivative[π](log(Probability[a:π](a[t].surrogate | s[t].surrogate))) * Q_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t]))) + \
                 γ ** n * Expectation(Derivative[π](V_st_var._subs(s[t].var, s[n]))))




@prove
def prove(Eq):
    from axiom import stats, calculus, keras, algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    π = Symbol(shape=(D,), real=True) #trainable weights for the agent
    t = Symbol(integer=True) #time step counter
    V, Q = Function(real=True, shape=()) #State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    n = Symbol(integer=True, nonnegative=True, given=False)
    *Eq[-3:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Lamda[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])), n)

    Eq << Eq[2].subs(t, 0)

    Eq << Eq[-1].subs(s[0].var, s[0])

    Eq << stats.eq.imply.eq.expect.apply(Eq[-1])

    Eq << Eq[-1].this.find(MatMul).apply(stats.matmul.to.expect)

    Eq << Eq[-1].this.rhs.apply(stats.expect.law_of_total_expectation)

    Eq << calculus.eq.imply.eq.grad.apply(Eq[-1], [π])

    Eq << Eq[-1].this.lhs.apply(stats.grad_expect.to.expect.grad).reversed

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    Eq << keras.eq_conditioned.eq_expect.eq_expect.imply.eq.grad.policy_gradient.induct.apply(*Eq[:3], n)

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

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(stats.expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Sum[~Mul[Expectation]]).apply(stats.mul.to.expect)

    Eq << Eq[-1].this.find(Sum[Expectation]).apply(stats.sum_expect.to.expect.sum)

    Eq << Eq[-1].this.lhs.find(Expectation).apply(stats.expect.to.matmul)

    Eq << Eq[-1].this.lhs.apply(calculus.grad_matmul.to.matmul.grad)

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
# created on 2023-04-04
# updated on 2023-04-12
