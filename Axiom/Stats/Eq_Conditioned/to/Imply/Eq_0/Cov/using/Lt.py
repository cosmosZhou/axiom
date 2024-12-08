from util import *


@apply
def apply(eq, i):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random
    return Imply(i < t, Equal(Covariance(s[i], r[t]), ZeroMatrix(*s[i].shape).outer_product(ZeroMatrix(*r[t].shape))))


@prove
def prove(Eq):
    from Axiom import Stats, Algebra

    s, r = Symbol(shape=(oo,), real=True, random=True)
    t, i = Symbol(integer=True) # time counter
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), i) # history-irrelevant conditional independence assumption

    Eq << Stats.Eq_Conditioned.to.All.Eq_Conditioned.independence_assumption.apply(Eq[0], i)

    Eq << Eq[-1].this.expr.apply(Stats.Eq_Conditioned.to.Eq_0.Cov)

    Eq << Algebra.Imply.of.All.apply(Eq[1], i)

    Eq << Algebra.All.of.All.limits.domain_defined.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-19
