from util import *


@apply
def apply(given, i=None, j=None):
    (xk, (k, a, b)), n = given.of(Equal[Cup[FiniteSet], Range[0]])
    assert b - a == n

    x = Lamda[k:a:b](xk).simplify()

    if j is None:
        j = Symbol(domain=Range(n), given=True)

    if i is None:
        i = Symbol(domain=Range(n), given=True)

    assert 0 <= j < n
    assert 0 <= i < n

    return Equal(KroneckerDelta(x[i], x[j]), KroneckerDelta(i, j))


@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), integer=True, given=True)
    k = Symbol(integer=True)
    i, j = Symbol(domain=Range(n), given=True)
    Eq << apply(Equal(x[:n].cup_finiteset(k), Range(n)), i, j)

    Eq << Eq[-1].apply(Algebra.Cond.of.And.Or, cond=Equal(i, j))

    Eq << Algebra.And.of.And.apply(Eq[-1])

    Eq <<= ~Eq[-1], ~Eq[-2]

    Eq << Eq[-2].apply(Algebra.Eq.Ne.to.Ne.subs)

    Eq << Eq[-1].this.apply(Algebra.Ne.Cond.to.Cond.subs, ret=0)

    Eq << Eq[0].apply(Sets.Eq.to.Eq.Card)

    Eq << Sets.Eq.to.All.Ne.Complement.apply(Eq[-1])

    Eq << Eq[-1].subs(Eq[-1].lhs.index, j)

    Eq << Eq[-1].this.expr.reversed

    Eq << Algebra.All.to.Or.subs.apply(Eq[-1], Eq[-1].variable, i)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()

# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-10-24
