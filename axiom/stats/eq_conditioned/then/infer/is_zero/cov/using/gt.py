from util import *


@apply
def apply(eq, i, swap=False):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random
    if swap:
        s, r = r, s
    return Infer(t > i, Equal(Covariance(r[t], s[i]), ZeroMatrix(*r[t].shape).outer_product(ZeroMatrix(*s[i].shape))))


@prove
def prove(Eq):
    from axiom import stats, algebra

    s, r = Symbol(shape=(oo,), real=True, random=True)
    t, i = Symbol(integer=True) # time counter
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), i) # history-irrelevant conditional independence assumption

    Eq << stats.eq_conditioned.then.all.eq_conditioned.independence_assumption.apply(Eq[0], i)

    Eq << Eq[-1].this.expr.apply(stats.eq_conditioned.then.is_zero.cov, swap=True)

    Eq << algebra.infer.of.all.apply(Eq[1], i)

    Eq << algebra.all.of.all.limits.domain_defined.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-19
