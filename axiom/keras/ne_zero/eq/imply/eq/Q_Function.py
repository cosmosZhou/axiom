from util import *


@apply
def apply(ne_zero, eq, γ=None, k=None):
    ((a, S[a.var]), (s, S[s.var])), (S[a], θ) = ne_zero.of(Unequal[Probability[Equal & Equal], 0])
    ((r, t), S[s[:t] & a[:t]]), S[r[t + 1]] = eq.of(Equal[Conditioned[Indexed[Symbol, Symbol + 1]]])

    if k is None:
        k = Symbol(integer=True) #time counter

    if γ is None:
        γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;

    assert γ >= 0 and γ < 1
    assert s.is_random and r.is_random

    st = s[t].as_boolean(surrogate=True)
    at = a[t].as_boolean(surrogate=True)
    prob = Probability[a:θ](at, given=st)
    return Equal(Expectation(Derivative[θ](log(prob)) * Sum[k:0:oo](γ ** k * r[t + k + 1])),
                 Expectation(Derivative[θ](log(prob)) * Expectation(Sum[k:0:oo](γ ** k * r[t + k + 1]) | at & st)))


@prove
def prove(Eq):
    from axiom import stats, discrete

    b, D = Symbol(integer=True, positive=True)
    θ = Symbol(real=True, shape=(D,))
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time counter
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    Eq << apply(
        Unequal(Probability[a:θ](a, s), 0),
        Equal(r[t + 1] | a[:t] & s[:t], r[t + 1]), #conditional independence assumption
        γ, k)

    Eq << Eq[-1].lhs.this.apply(stats.expect.law_of_iterated_expectation, a[:t + 1], s[:t + 1])

    Eq << Eq[-1].this.rhs.find(Expectation[Conditioned]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Expectation[Conditioned]).apply(stats.expect_sum.to.sum.expect)

    Eq << Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(stats.expect.to.mul)

    Eq << Eq[-1].this.find(Sum[Pow * Expectation]).apply(discrete.sum.to.matmul)

    Eq << Eq[-1].this.find(Lamda[Expectation]).apply(stats.lamda_expect.to.expect.lamda)

    Eq << stats.eq.imply.eq.independence_assumption.bidirectional.double.apply(Eq[1]).subs(t, t + 1)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Mul[Expectation]).apply(stats.mul.to.expect)

    Eq << Eq[-1].this.find(Sum[Expectation]).apply(stats.sum_expect.to.expect.sum)

    Eq << Eq[-1].this.rhs.simplify()
    #https://spinningup.openai.com/en/latest/spinningup/extra_pg_proof2.html




if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-02
