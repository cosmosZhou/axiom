from util import *


@apply
def apply(given):
    (all_historic, all_n), (i, S[0], n) = given.of(All[And])
    if all_n.is_ForAll:
        all_n, all_historic = all_historic, all_n

    (lhs, rhs), (j, S[0], S[i]) = all_historic.of(All[Unequal])

    if lhs._has(j):
        lhs, rhs = rhs, lhs

    x = Lamda[i:n + 1](lhs)
    assert x[j] == rhs

    lhs, rhs = all_n.of(Unequal)
    if lhs._has(i):
        lhs, rhs = rhs, lhs

    assert x[n] == lhs
    assert x[i] == rhs

    return All[j:i, i:n + 1](Unequal(x[i], x[j]))


@prove
def prove(Eq):
    from axiom import algebra, sets

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    Eq << apply(All[i:n](Unequal(x[n], x[i]) & All[j:i](Unequal(x[i], x[j]))))

    Eq << algebra.all_et.imply.et.all.apply(Eq[0])

    Eq << sets.all_ne.all_ne.imply.all.ne.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()

# created on 2021-01-11
