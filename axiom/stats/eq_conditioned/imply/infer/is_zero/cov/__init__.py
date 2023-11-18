from util import *


@apply
def apply(eq, i):
    ((x, t), ((S[x], (S[0], S[t])), S[x[:t].var])), S[x[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert x.is_random
    return Infer(Unequal(i, t), Equal(Covariance(x[t], x[i]), ZeroMatrix(*x[t].shape).outer_product(ZeroMatrix(*x[i].shape))))


@prove
def prove(Eq):
    from axiom import algebra, stats

    x = Symbol(shape=(oo,), real=True, random=True)
    t, i = Symbol(integer=True) # time counter
    Eq << apply(
        Equal(x[t] | x[:t], x[t]), i) # history-irrelevant conditional independence assumption

    Eq << Eq[1].this.lhs.apply(algebra.ne.imply.ou)

    Eq << algebra.infer_ou.given.et.infer.apply(Eq[-1])

    Eq << stats.eq_conditioned.imply.infer.is_zero.cov.using.gt.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.reversed

    Eq << stats.eq_conditioned.imply.infer.is_zero.cov.using.lt.apply(Eq[0], i)

    j = Symbol(integer=True) # time counter
    Eq << Eq[-1].subs(i, j)

    Eq << Eq[-1].subs(t, i)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].subs(j, t)

    


if __name__ == '__main__':
    run()
# created on 2023-04-19

from . import using
