from util import *


@apply
def apply(ne_zero, eq, γ=None, k=None, weights=None):
    (a, S[a.var]), (s, S[s.var]) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])
    ((r, (t, S[oo])), S[s[t] & a[t]]), S[r[t + 2:]] = eq.of(Equal[Conditioned[Sliced[Symbol, Tuple[Symbol + 2]]]])

    if k is None:
        k = Symbol(integer=True) #time countor

    if γ is None:
        γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;

    assert s.is_random and r.is_random
    if weights:
        limits_curr = [(r[t + 1:],), weights]
        limits_next = [(r[t + 2:],), weights]
        limits_coeff = [(r[t + 1],), weights]
    else:
        limits_curr = []
        limits_next = []
        limits_coeff = []

    return Equal(Expectation(Sum[k:0:oo](γ ** k * r[t + k + 1]) | s[t] & a[t], *limits_curr),
                 Expectation((γ * Expectation(Sum[k:0:oo](γ ** k * r[t + k + 2]), *limits_next, given=Equal(s[t + 1], s[t + 1].surrogate)) + r[t + 1]) | s[t] & a[t], *limits_coeff))


@prove
def prove(Eq):
    from axiom import stats, calculus, keras, algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time countor
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    Eq << apply(
        Unequal(Probability(a, s), 0),
        Equal(r[t + 2:] | s[t] & a[t], r[t + 2:]), #conditional independence assumption
        γ, k)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.add)

    Eq << Eq[-1].this.find(Expectation[2]).apply(stats.expect.to.integral)

    Eq.final = Eq[-1].this.find(Integral[Mul]).apply(calculus.integral.to.mul)

    Eq << Eq.final.lhs.this.find(Sum).apply(keras.sum.to.add.sum.discounted_future_reward)

    Eq << Eq[-1].this.rhs.apply(stats.expect.to.add)

    Eq.eq_add = Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(stats.expect.to.mul)

    Eq << Eq.eq_add.find(Mul[~Expectation]).this.apply(stats.expect.to.integral)

    Eq << Eq[-1].this.find(Probability).apply(stats.prob.to.integral.joint, s[t + 1])

    Eq << Eq[-1].this.find(Mul[Integral]).apply(calculus.mul.to.integral)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.swap)

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[0], [t, slice(t, t + 2)])

    Eq.joint_ne_zero = Eq[-1].this.find(Equal[Sliced]).apply(algebra.eq.to.et.eq.split)

    Eq << stats.ne_zero.imply.eq.bayes.conditioned.st.joint.apply(Eq.joint_ne_zero, s[t + 1], r[t + 2:])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(calculus.integral.limits.separate)

    Eq << stats.ne_zero.eq.imply.eq.conditioned.joint.apply(Eq[1], Eq.joint_ne_zero)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq.final.rhs.find(Mul[~Expectation]).this.apply(stats.expect.to.integral)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq.eq_add.subs(Eq[-1])

    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Bellman equation Eq. 3.14)



if __name__ == '__main__':
    run()
# created on 2023-03-29
