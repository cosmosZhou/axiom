from util import *


@apply
def apply(given, j=None):
    from Axiom.Discrete.Eq.to.And.index import index_function
    x_cup_finiteset, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0

    arg, (k, a, S[a + n]) = x_cup_finiteset.of(Cup[FiniteSet])
    x = Lamda[k:a:a + n](arg).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n

    index = index_function(n)

    return Equal(index[x[j]](x[:n]), j)


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets

    n = Symbol(domain=Range(2, oo), given=True)
    x = Symbol(shape=(oo,), integer=True, given=True)
    k = Symbol(integer=True)
    j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), j)

    t, i = Symbol(domain=Range(n))
    Eq << Discrete.Eq.to.And.index.apply(Eq[0], j=t)

    Eq.ou = Algebra.Cond.to.Or.subs.apply(Eq[-1], t, x[j])

    Eq.equality = Eq.ou.args[0].copy(plausible=True)

    Eq.xj_notcontains = Eq.ou.args[1].copy(plausible=True)

    Eq << Sets.Eq.to.Subset.apply(Eq[0])

    Eq << Sets.Subset_Cup.to.All_Subset.apply(Eq[-1])

    Eq << Algebra.All.to.Cond.subs.apply(Eq[-1], Eq[-1].variable, j)

    Eq <<= Eq[-1] & Eq.xj_notcontains

    Eq << Discrete.Eq.to.Eq.index.Delta.Indexed.apply(Eq[0], i, j)

    Eq.ou1 = Algebra.Cond.to.Or.subs.apply(Eq[-1], i, Eq[1].lhs)

    Eq.ou2 = Algebra.Cond.to.Or.subs.apply(Eq[2], t, x[j])

    Eq.index_contains = Eq.ou2.args[0].copy(plausible=True)

    Eq <<= Eq.ou & ~Eq.xj_notcontains

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=0)

    Eq <<= Eq.ou2 & ~Eq.xj_notcontains

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=1)

    Eq <<= Eq.ou1 & Eq.index_contains

    Eq << Algebra.And.to.Cond.apply(Eq[-1], index=0)

    Eq << Eq[-1].subs(Eq.equality)

    Eq << Eq[-1].this.apply(Algebra.Eq.simp.Delta)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html

# created on 2020-10-26
# updated on 2023-05-15
