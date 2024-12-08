from util import *


@apply
def apply(eq):
    ((s, k), S[s[:k].as_boolean()]), (S[s[k]], S[s[k - 1].as_boolean()]) = eq.of(Equal[Conditioned[Indexed], Conditioned])
    assert s.is_random
    return Equal(Probability(s[k + 1] | s[k]) * Probability(s[k] | s[0]),
                 Probability(s[k + 1] & s[k] | s[0]))


@prove
def prove(Eq):
    from Axiom import Algebra, Stats, Calculus

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    Eq << apply(Equal(s[k] | s[:k], s[k] | s[k - 1]))

    Eq << Algebra.Cond.to.Cond.domain_defined.apply(Eq[0])

    Eq << Algebra.And.to.Cond.apply(Eq[-1], 0)

    Eq <<= Eq[-1].subs(k, 1), Eq[-1].subs(k, k + 1)

    Eq << Eq[1].this.lhs.find(Probability).apply(Stats.Prob.eq.Integral.joint, s[1:k])

    Eq << Eq[-1].this.lhs.find(Equal & Equal).apply(Algebra.Eq.Eq.equ.Eq.concat)

    Eq << Stats.Eq.to.Eq.Prod.markov.first_order.apply(Eq[0], k)
    Eq << Eq[-2].subs(Eq[-1])
    Eq << Algebra.And.of.And.apply(Eq[-1], None)
    Eq << Eq[-1].this.lhs.apply(Calculus.Mul.eq.Integral)
    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Prod.limits.push)
    Eq << Eq[-1].this.rhs.apply(Stats.Prob.eq.Integral.joint, s[1:k])
    Eq << Eq[-1].this.find(And).args[::2].apply(Algebra.Eq.Eq.equ.Eq.concat)
    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.equ.Eq.concat)
    Eq << Stats.Eq.to.Eq.Prod.markov.first_order.apply(Eq[0], k + 1)
    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-12
