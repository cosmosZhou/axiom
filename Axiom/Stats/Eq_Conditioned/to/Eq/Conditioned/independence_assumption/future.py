from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random
    return Equal(r[t + 1:] | s[t], r[t + 1:])


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.oo.independence_assumption.apply(Eq[0])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Eq.equ.And.Eq.split)

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.getitem.apply(Eq[-1], s[t])





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-06
