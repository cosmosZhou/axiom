from util import *


@apply
def apply(eq, i):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random
    return All[i:t](Equal(r[t] | s[i], r[t]))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra, Sets

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True) # time counter
    i = Symbol(integer=True)
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), i) # history-irrelevant conditional independence assumption

    Eq << Stats.Eq_Conditioned.to.Eq.Conditioned.independence_assumption.future.apply(Eq[0])

    j = Symbol(integer=True, nonnegative=True)
    Eq << Eq[2][j]

    Eq << Algebra.Cond.to.All.apply(Eq[-1], j)

    Eq << Eq[-1].this.apply(Algebra.All.limits.subs.offset, -1)

    Eq << Eq[-1].this.apply(Algebra.All.limits.subs.offset, -t)

    j = Eq[-1].variable
    Eq << Algebra.All.to.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Le.of.Lt.One)

    Eq << Eq[-1].subs(t, i)

    Eq << Eq[-1].subs(j, t)



    Eq << Algebra.All.of.Imply.apply(Eq[1])

    Eq << Eq[-1].this.find(Element).apply(Sets.In_Range.to.Lt)




if __name__ == '__main__':
    run()
# created on 2023-04-19
