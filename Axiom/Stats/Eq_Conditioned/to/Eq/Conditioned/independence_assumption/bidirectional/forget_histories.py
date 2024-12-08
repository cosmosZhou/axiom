from util import *


@apply
def apply(eq):
    ((r, t), (((s, (S[0], S[t])), S[s[:t].var]), ((a, (S[0], S[t])), S[a[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    assert s.is_random and r.is_random and a.is_random

    return Equal(r[t:] | s[:t + 1] & a[:t + 1], r[t:] | s[t] & a[t])


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    t = Symbol(integer=True, positive=True) # time counter
    Eq << apply(
        Equal(r[t] | s[:t] & a[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.getitem.apply(Eq[0], 0)

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.oo.independence_assumption.apply(Eq[-1])

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.getitem.apply(Eq[0], 1)

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.oo.independence_assumption.apply(Eq[-1])

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq << Stats.Ne_0.Eq_Conditioned.Eq_Conditioned.to.Eq.Conditioned.joint.apply(Eq[-1], Eq[-2], Eq[-4])

    Eq << Eq[-2].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Eq.equ.And.Eq.split)

    Eq << Eq[-1].this.find(Equal[3]).apply(Algebra.Eq.equ.And.Eq.split)

    Eq << Stats.Ne_0.Eq_Conditioned.to.Eq.Conditioned.joint.apply(Eq[-1], Eq[-4])

    Eq << Eq[-1].this.find(And).args[::2].apply(Algebra.Eq.Eq.equ.Eq.concat)

    Eq << Eq[-1].this.find(And).args[::2].apply(Algebra.Eq.Eq.equ.Eq.concat)





if __name__ == '__main__':
    run()
# created on 2023-04-02
# updated on 2023-05-20
