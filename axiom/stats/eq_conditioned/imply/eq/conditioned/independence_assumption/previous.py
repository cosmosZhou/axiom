from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    assert s.is_random and r.is_random
    assert t >= 0
    return Equal(r[t:] | s[:t + 1], r[t:] | s[t])


@prove
def prove(Eq):
    from axiom import algebra, stats

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Eq[0].this.domain_definition()

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.et.eq.split)

    Eq << stats.eq_conditioned.imply.eq.conditioned.oo.independence_assumption.apply(Eq[0])

    Eq << stats.ne_zero.eq_conditioned.imply.eq.conditioned.joint.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(And).apply(algebra.eq.eq.to.eq.concat)





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
