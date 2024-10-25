from util import *


@apply
def apply(given, i=None, j=None):
    from axiom.discrete.eq.then.et.index import index_function
    x_cup_finiteset, interval = given.of(Equal)
    n = interval.max() + 1
    assert interval.min() == 0

    arg, (k, a, S[a + n]) = x_cup_finiteset.of(Cup[FiniteSet])
    x = Lamda[k:a:a + n](arg).simplify()


    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n
    assert 0 <= i < n

    index = index_function(n)

    di = index[i](x[:n])
    dj = index[j](x[:n])

    return Equal(KroneckerDelta(di, dj), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    j, i = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), i, j)

    Eq << Eq[-1].apply(algebra.cond.of.et.ou, cond=Equal(i, j))

    Eq << algebra.et.of.et.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(algebra.eq.ne.then.ne.subs)

    Eq << Eq[-1].this.apply(algebra.ne.cond.then.cond.subs, ret=0)

    Eq << discrete.eq.then.et.index.apply(Eq[0], j=j)[1]

    Eq << Eq[-2].this.args[1].rhs.subs(Eq[-1].reversed)

    Eq << discrete.eq.then.et.index.apply(Eq[0], j=i)[1]

    Eq << Eq[-2].this.args[1].lhs.subs(Eq[-1].reversed)

    Eq << Eq[-1].apply(algebra.eq.ne.then.ne.subs)





if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-25
# updated on 2023-05-20
