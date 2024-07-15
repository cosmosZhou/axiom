from util import *


@apply
def apply(Q_def):
    (discount, ((limit_rt, et), (S[limit_rt],), (a, π))), Q_st_var = Q_def.of(Equal[MatMul[Expectation[Conditioned]]])
    r, (t, S[oo]) = limit_rt.of(Sliced)
    ((S[a], S[t]), S[a[t].var]), ((s, S[t]), S[s[t].var]) = et.of(Equal[Indexed] & Equal[Indexed])
    γ, (k, [S[k]]) = discount.of(Pow[Lamda])

    assert a.is_random and s.is_random and r.is_random
    S[s[t].var], S[a[t].var], [S[π]], [S[γ]] = Q_st_var.of(Function)

    return Equal(discount @ Expectation[r[t:], a:π](r[t:] | s[t]), Expectation[a[t]:π](Q_st_var._subs(a[t].var, a[t]) | s[t]))


@prove
def prove(Eq):
    from axiom import algebra, stats, calculus

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t, k = Symbol(integer=True) # time countor
    Q = Function(real=True, shape=()) # Action-Value Function
    γ = Symbol(domain=Interval(0, 1, left_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Lamda[k](k) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])))

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0])

    Eq << stats.ne_zero.imply.et.ne_zero.apply(Eq[-1])

    Eq << Eq[1].this.rhs.apply(stats.expect.to.sum)

    Eq << Eq[-1].subs(Eq[0])

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.find(Sum[Integral]).apply(calculus.sum.to.integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)

    Eq << Eq[-1].this.find(Pow @ Integral).apply(calculus.matmul.to.integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << stats.ne_zero.imply.eq.prob.conditioned.to.mul.prob.conditioned.bayes.apply(Eq[2], a[t], r[t:])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << algebra.et.given.et.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.sum.to.integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)

    Eq << Eq[-1].this.find(Expectation).apply(stats.expect.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(calculus.sum.to.integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)


    Eq << Eq[-1].this.lhs.apply(calculus.matmul.to.integral)
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# bellman-equations
    # https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# id4
    # https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    # https://www.52coding.com.cn/tags/Reinforcement-Learning/
    # TRPO
    # https://arxiv.org/pdf/1502.05477.pdf




if __name__ == '__main__':
    run()
# created on 2023-03-29
# updated on 2023-04-27
from . import normalized
