from util import *


@apply
def apply(given, n):
    (xi, xj), (j, (i, _j)) = given.of(All[Equal[Intersection, EmptySet], Tuple[Unequal]])
    if j != _j:
        i, S[j] = _j, i

    if not xi.has(i):
        xi = xj
        assert xj.has(i)

    assert xj._subs(j, i) == xi

    return Equal(Card(Cup[i:n](xi)), Sum[i:n](Card(xi)))


@prove
def prove(Eq):
    from axiom import sets, algebra
    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo), given=False)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)

    Eq << apply(All(Equal(x[i] & x[j], x[i].etype.emptySet), (j, Unequal(j, i))), n)

    Eq << algebra.all.then.infer.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(algebra.ne.of.lt)

    j_ = Symbol('j', integer=True, nonnegative=True)
    Eq << Eq[-1].subs(j, j_)

    Eq << algebra.infer.then.all.apply(Eq[-1])

    Eq << sets.all_is_empty.then.eq.nonoverlapping.intlimit.utility.apply(Eq[-1], n)


if __name__ == '__main__':
    run()

# created on 2021-01-12
