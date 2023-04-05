from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t - 1])), S[s[:t - 1].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    t -= 1
    assert s.is_random and r.is_random
    assert t > 0
    return Equal(r[t + 2:] | s[t], r[t + 2:])


@prove
def prove(Eq):
    from axiom import stats, algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #rewards
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t = Symbol(integer=True, positive=True) #time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t + 1] | s[:t], r[t + 1])) #conditional independence assumption

    Eq << stats.eq.imply.eq.independence_assumption.bidirectional.apply(Eq[0])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.et.eq.split)

    Eq << stats.eq.imply.eq.single_condition.apply(Eq[-1], s[t])

    


if __name__ == '__main__':
    run()
# created on 2023-04-01
