from util import *


@apply
def apply(eq):
    ((s, k), S[s[:k].as_boolean()]), (S[s[k]], S[s[k - 1].as_boolean()]) = eq.of(Equal[Conditioned[Indexed], Conditioned])
    assert s.is_random
    return Equal(Probability(s[k + 1] | s[k]) * Probability(s[k] | s[0]),
                 Probability(s[k + 1] & s[k] | s[0]))


@prove
def prove(Eq):
    from axiom import algebra, stats, calculus

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    Eq << apply(Equal(s[k] | s[:k], s[k] | s[k - 1]))

    Eq << algebra.cond.then.cond.domain_defined.apply(Eq[0])

    Eq << algebra.et.then.cond.apply(Eq[-1], 0)

    Eq <<= Eq[-1].subs(k, 1), Eq[-1].subs(k, k + 1)

    Eq << Eq[1].this.lhs.find(Probability).apply(stats.prob.to.integral.joint, s[1:k])

    Eq << Eq[-1].this.lhs.find(Equal & Equal).apply(algebra.eq.eq.to.eq.concat)

    Eq << stats.eq.then.eq.prod.markov.first_order.apply(Eq[0], k)
    Eq << Eq[-2].subs(Eq[-1])
    Eq << algebra.et.of.et.apply(Eq[-1], None)
    Eq << Eq[-1].this.lhs.apply(calculus.mul.to.integral)
    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.prod.limits.push)
    Eq << Eq[-1].this.rhs.apply(stats.prob.to.integral.joint, s[1:k])
    Eq << Eq[-1].this.find(And).args[::2].apply(algebra.eq.eq.to.eq.concat)
    Eq << Eq[-1].this.find(And).apply(algebra.eq.eq.to.eq.concat)
    Eq << stats.eq.then.eq.prod.markov.first_order.apply(Eq[0], k + 1)
    Eq << Eq[-2].subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-12
