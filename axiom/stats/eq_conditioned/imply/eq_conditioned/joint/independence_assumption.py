from util import *


@apply
def apply(eq):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    #assert t >= 0
    assert s.is_random and r.is_random and a.is_random
    return Equal(r[t + 1:] | s[t] & a[t], r[t + 1:])


@prove
def prove(Eq):
    from axiom import stats, algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #states
    a = Symbol(shape=(oo,), integer=True, random=True) #actions
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t = Symbol(integer=True, positive=True) #time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t] & a[:t], r[t])) #history-irrelevant conditional independence assumption

    Eq << stats.eq_conditioned.imply.eq_conditioned.getitem.apply(Eq[0])

    Eq << stats.eq_conditioned.imply.eq_conditioned.oo.independence_assumption.apply(Eq[-1])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.et.eq.split)

    Eq.eq_at = stats.eq_conditioned.imply.eq_conditioned.getitem.apply(Eq[-1], 0)

    Eq << stats.eq_conditioned.imply.eq_conditioned.getitem.apply(Eq[0], 1)

    Eq << stats.eq_conditioned.imply.eq_conditioned.oo.independence_assumption.apply(Eq[-1])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.et.eq.split)

    Eq.eq_st = stats.eq_conditioned.imply.eq_conditioned.getitem.apply(Eq[-1], 0)

    Eq << algebra.cond.imply.cond.domain_defined.apply(Eq[0])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(algebra.eq.to.et.eq.split)

    Eq << Eq[-1].this.find(Equal[3]).apply(algebra.eq.to.et.eq.split)

    Eq << stats.ne_zero.imply.ne_zero.delete.apply(Eq[-1], slice(2, None))

    Eq << stats.ne_zero.eq_conditioned.eq_conditioned.imply.eq.conditioned.joint.apply(Eq[-1], Eq.eq_at, Eq.eq_st)

    
    


if __name__ == '__main__':
    run()
# created on 2023-04-05
# updated on 2023-05-20
