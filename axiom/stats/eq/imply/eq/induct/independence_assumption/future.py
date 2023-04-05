from util import *


@apply
def apply(eq, k):
    ((r, t), ((s, (S[0], S[t - 1])), S[s[:t - 1].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    t -= 1
    assert s.is_random and r.is_random
    assert k > 0 and t > 0
    return Equal(r[t + 1:t + k + 1] | s[:t], r[t + 1:t + k + 1])


@prove
def prove(Eq):
    from axiom import stats, algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) #rewards
    r = Symbol(shape=(oo,), real=True, random=True) #rewards
    t = Symbol(integer=True, positive=True) #time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t + 1] | s[:t], r[t + 1]), k) #conditional independence assumption

    Eq << Eq[1].subs(k, 1)

    Eq.induct = Eq[1].subs(k, k + 1)

    Eq << stats.eq.imply.eq.induct.independence_assumption.historic.apply(Eq[0], k + 1)

    Eq << stats.eq.eq.imply.eq.joint.apply(Eq[1], Eq[2])

    Eq << Eq[-1].this.find(And).apply(algebra.et_eq.to.eq.concat)

    Eq << Eq[-1].this.find(And).apply(algebra.et_eq.to.eq.concat)

    Eq << Infer(Eq[1], Eq.induct, plausible=True)

    Eq << algebra.eq.infer.imply.eq.induct.apply(Eq[0], Eq[-1], k, start=1)

    


if __name__ == '__main__':
    run()
# created on 2023-04-01
