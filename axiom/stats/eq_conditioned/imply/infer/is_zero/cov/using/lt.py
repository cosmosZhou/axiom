from util import *


@apply
def apply(eq, i):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    #assert t >= 0
    assert s.is_random and r.is_random
    return Infer(i < t, Equal(Covariance(s[i], r[t]), ZeroMatrix(*s[i].shape).outer_product(ZeroMatrix(*r[t].shape))))


@prove
def prove(Eq):
    from axiom import stats, algebra

    s, r = Symbol(shape=(oo,), real=True, random=True)
    t, i = Symbol(integer=True) #time counter
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), i) #history-irrelevant conditional independence assumption

    Eq << stats.eq_conditioned.imply.all.eq_conditioned.independence_assumption.apply(Eq[0], i)

    Eq << Eq[-1].this.expr.apply(stats.eq_conditioned.imply.is_zero.cov)

    Eq << algebra.infer.given.all.apply(Eq[1], i)

    Eq << algebra.all.given.all.limits.domain_defined.apply(Eq[-1])

    


if __name__ == '__main__':
    run()
# created on 2023-04-19
