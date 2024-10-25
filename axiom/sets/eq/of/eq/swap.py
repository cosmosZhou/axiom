from util import *


@apply
def apply(imply, i=None, j=None):
    from axiom.sets.then.eq.swap import swap
    x, y = imply.of(Equal)
    n, = x.shape

    assert x.dtype.is_set
    if i is None:
        i = Symbol(integer=True)

    if j is None:
        j = Symbol(integer=True)

    return Equal(swap[i, j](x), swap[i, j](y))


@prove
def prove(Eq):
    from axiom import sets, algebra
    n = Symbol(positive=True, integer=True)

    x, y = Symbol(shape=(n,), etype=dtype.integer)

    Eq << apply(Equal(x, y))

    (i,), (j,) = Eq[1].lhs.limits
    Eq << sets.eq.then.eq.swap.apply(Eq[1], i, j)

    Eq << sets.then.eq.swap.apply(x, i, j)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-2], Eq[-1])

    Eq << sets.then.eq.swap.apply(y, i, j)

    Eq << algebra.eq.eq.then.eq.trans.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2021-03-30
