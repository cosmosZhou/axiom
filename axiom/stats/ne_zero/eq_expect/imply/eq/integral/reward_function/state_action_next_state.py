from util import *


@apply
def apply(ne_zero, r_expected_def):
    (((r, t), (((a, S[t - 1]), S[a[t - 1].var]), ((s, S[t - 1]), S[s[t - 1].var]), S[s[t].as_boolean()])), (S[r[t]],)), r_st = r_expected_def.of(Equal[Expectation[Conditioned[Indexed, Equal[Indexed] & Equal[Indexed]]]])
    assert s.is_random and a.is_random and r.is_random
    S[s & a] = ne_zero.of(Unequal[Probability, 0])

    return Equal(r_st, Integral[r[t].var](r[t].var * Probability(s[t] & r[t], given=s[t - 1] & a[t - 1]) / Probability(s[t] | s[t - 1] & a[t - 1])))



@prove
def prove(Eq):
    from axiom import stats, algebra

    b = Symbol(integer=True, positive=True)
    #states / observation of the agent
    s = Symbol(shape=(oo, b), real=True, random=True)
    #actions to take by the agent
    a = Symbol(shape=(oo,), integer=True, random=True)
    #rewards from the environment
    r = Symbol(shape=(oo,), real=True, random=True)
    #discrete time step
    t = Symbol(integer=True)
    r_expected = Function(r'\textbf{r}', shape=(), real=True)
    Eq << apply(
        Unequal(Probability(s, a), 0),
        Equal(r_expected[t](s[t - 1].var, a[t - 1].var, s[t].var), Expectation[r[t]](r[t] | s[t - 1] & a[t - 1] & s[t])),)

    Eq << Eq[1].this.rhs.apply(stats.expect.to.integral)

    Eq << stats.ne_zero.imply.ne_zero.joint_slice.apply(Eq[0], ([t - 1, slice(t - 1, t + 1)]))

    Eq << Eq[-1].this.find(Equal[Sliced]).apply(algebra.eq.to.et.eq.split)

    Eq << stats.ne_zero.imply.ne_zero.conditioned.apply(Eq[-1], a[t - 1], s[t - 1])
    Eq << stats.ne_zero.imply.eq.bayes.conditioned.apply(Eq[-1], r[t])

    Eq << algebra.ne_zero.eq.imply.eq.div.apply(Eq[-2], Eq[-1])

    Eq << Eq[3].subs(Eq[-1].reversed)

    #the expected rewards for state–action–next-state triples as a three-argument function r
    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Eq. 3.6)



if __name__ == '__main__':
    run()
# created on 2023-03-27
