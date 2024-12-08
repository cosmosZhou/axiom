from util import *


@apply
def apply(imply, i=None, j=None):
    from Axiom.Sets.EqSwapSwap import swap
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
    from Axiom import Sets, Algebra
    n = Symbol(positive=True, integer=True)

    x, y = Symbol(shape=(n,), etype=dtype.integer)

    Eq << apply(Equal(x, y))

    (i,), (j,) = Eq[1].lhs.limits
    Eq << Sets.Eq.to.Eq.swap.apply(Eq[1], i, j)

    Eq << Sets.EqSwapSwap.apply(x, i, j)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])

    Eq << Sets.EqSwapSwap.apply(y, i, j)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2021-03-30
