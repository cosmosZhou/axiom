from util import *


@apply
def apply(eq, n):
    ((s, k), S[s[:k].as_boolean()]), (S[s[k]], S[s[k - 1].as_boolean()]) = eq.of(Equal[Conditioned[Indexed], Conditioned])
    t, = k.free_symbols
    start = k - t
    stop = n + start
    assert s.is_random
    return Equal(Probability(s[1:n + 1] | s[0]),
                 Product[t:start + 1:stop + 1](Probability(s[k] | s[k - 1])))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, positive=True)  # total time step
    Eq << apply(Equal(s[k] | s[:k], s[k] | s[k - 1]), n)

    Eq << Stats.Eq.to.Eq.Prob.apply(Eq[0], simplify=False)

    Eq << Algebra.Eq.to.Eq.Prod.apply(Eq[-1], (k, 1, n + 1))

    Eq << Eq[-1].this.find(Probability).apply(Stats.Prob.eq.Div.Prob.bayes)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.equ.Eq.concat)

    Eq << Eq[-1].this.find(Equal[Sliced]).apply(Algebra.Eq.equ.And.Eq.split, 1)

    Eq << Eq[1].this.lhs.apply(Stats.Prob.eq.Div.Prob.bayes)


if __name__ == '__main__':
    run()
# created on 2023-03-30
