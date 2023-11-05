from util import *


@apply
def apply(eq, γ=None, k=None, weights=None):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    if k is None:
        k = Symbol(integer=True) #time countor

    if γ is None:
        γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1

    assert s.is_random and r.is_random and a.is_random
    if weights:
        limits_curr = [(r[t:],), weights]
        limits_next = [(r[t + 1:],), weights]
        limits_coeff = [(r[t],), (s[t + 1],), weights]
    else:
        limits_curr = []
        limits_next = []
        limits_coeff = []

    return Equal(γ ** Lamda[k](k) @ Expectation(r[t:] | s[t] & a[t], *limits_curr),
                 Expectation((γ * γ ** Lamda[k](k) @ Expectation(r[t + 1:], *limits_next, given=Equal(s[t + 1], s[t + 1].surrogate)) + r[t]) | s[t] & a[t], *limits_coeff))


@prove
def prove(Eq):
    from axiom import stats, calculus, keras, algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time countor
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(
        Equal(r[t] | s[:t] & a[:t], r[t]), #history-irrelevant conditional independence assumption for rewards based on states and actions
        γ, k)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[2]).apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Integral[Mul]).apply(calculus.integral.to.mul)

    Eq.final = Eq[-1].this.lhs.apply(stats.matmul.to.expect)

    Eq << Eq.final.lhs.this.find(MatMul).apply(keras.matmul.to.add.mul.matmul.discounted_future_reward)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.add)

    Eq.eq_add = Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(stats.expect.to.mul)

    Eq << Eq.eq_add.find(Mul[~Expectation]).this.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Probability).apply(stats.prob.to.integral.joint, s[t + 1])

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.find(Probability).apply(stats.prob.conditioned.to.mul.prob.conditioned)

    Eq.eq_expect = Eq[-1].this.rhs.apply(calculus.integral.limits.separate)

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0]).subs(t, t + 1)

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[-1], [t, slice(t, t + 2)])

    Eq << Eq[-1].this.find(Equal[Sliced]).apply(algebra.eq.to.et.eq.split)

    Eq << stats.eq_conditioned.imply.eq_conditioned.joint.independence_assumption.apply(Eq[0])

    Eq << stats.ne_zero.eq_conditioned.imply.eq.conditioned.joint.apply(*Eq[-2:])

    Eq << Eq.eq_expect.subs(Eq[-1])

    Eq << Eq.final.rhs.find(MatMul).this.apply(stats.matmul.to.expect)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.integral)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Eq.eq_add.subs(Eq[-1])

    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Bellman equation Eq. 3.14)
    #http://incompleteideas.net/book/RLbook2020.pdf
    #http://incompleteideas.net/book/the-book-2nd.html
    
    


if __name__ == '__main__':
    run()
# created on 2023-03-29
# updated on 2023-10-14
from . import normalized
