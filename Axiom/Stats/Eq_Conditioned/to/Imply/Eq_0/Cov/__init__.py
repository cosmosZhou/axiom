from util import *


@apply
def apply(eq, i):
    ((x, t), ((S[x], (S[0], S[t])), S[x[:t].var])), S[x[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert x.is_random
    return Imply(Unequal(i, t), Equal(Covariance(x[t], x[i]), ZeroMatrix(*x[t].shape).outer_product(ZeroMatrix(*x[i].shape))))


@prove
def prove(Eq):
    from Axiom import Algebra, Stats

    x = Symbol(shape=(oo,), real=True, random=True)
    t, i = Symbol(integer=True) # time counter
    Eq << apply(
        Equal(x[t] | x[:t], x[t]), i) # history-irrelevant conditional independence assumption

    Eq << Eq[1].this.lhs.apply(Algebra.Ne.to.Or)

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq << Stats.Eq_Conditioned.to.Imply.Eq_0.Cov.using.Gt.apply(Eq[0], i)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Stats.Eq_Conditioned.to.Imply.Eq_0.Cov.using.Lt.apply(Eq[0], i)

    j = Symbol(integer=True) # time counter
    Eq << Eq[-1].subs(i, j)

    Eq << Eq[-1].subs(t, i)

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].subs(j, t)




if __name__ == '__main__':
    run()
# created on 2023-04-19

from . import using
