from util import *


@apply
def apply(self):
    ((((γ, k), (r, (S[k], t))), (S[k], S[0], S[oo])), ((s, S[t]), S[s[t].var])), [S[r[t + 1:]]], [S[s[t + 1:]]], (at,) = self.of(Expectation[Conditioned[Sum[Pow * Indexed[Symbol, Add[1]]], Equal[Indexed]]])
    a, (S[t], S[oo]) = at.of(Sliced)
    assert a.is_random and s.is_random and r.is_random
    return Equal(self, 
                 Integral[r.var[t + 1:]](Probability(r[t + 1:] | s[t]) * Sum[k:0:oo](γ ** k * r.var[k + t + 1])))


@prove
def prove(Eq):
    from axiom import stats, calculus

    b, D = Symbol(domain=Range(2, oo))
    #D denotes the size of the trainable weights
    s = Symbol(shape=(oo, b), real=True, random=True) #states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t, k = Symbol(integer=True) #time countor
    γ = Symbol(domain=Interval(0, 1, right_open=True)) #Discount factor; penalty to uncertainty of future rewards;
    Eq << apply(Expectation[r[t + 1:], s[t + 1:], a[t:]](Sum[k:0:oo](γ ** k * r[t + k + 1]) | s[t]))

    Eq << Eq[-1].lhs.this.apply(stats.expect.to.sum)

    Eq << Eq[-1].this.rhs.apply(calculus.sum.to.integral)

    Eq << Eq[-1].this.find(Sum[Probability]).apply(stats.sum.to.prob)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.swap)

    Eq << Eq[-1].this.find(Integral).apply(calculus.integral.limits.separate)

    Eq << Eq[-1].this.find(Mul[~Integral]).apply(stats.integral.to.prob)

    #http://incompleteideas.net/book/bookdraft2017nov5.pdf (Bellman equation Eq. 3.14)
    


if __name__ == '__main__':
    run()
# created on 2023-03-27
