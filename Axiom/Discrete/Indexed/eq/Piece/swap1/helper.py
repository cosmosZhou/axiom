from util import *


@apply
def apply(x, w=None):
    n = x.shape[0]
    i, j = Symbol(integer=True)

    if w is None:
        w = Symbol(Lamda[j](SwapMatrix(n, 0, j)))

    assert w.shape == (n, n, n)
    assert w[j].definition == SwapMatrix(n, 0, j)

    return Equal(Lamda[i:n](x[w[j][i] @ Lamda[i:n](i)]), Lamda[i:n](Piecewise((x[0], Equal(i, j)), (x[j], Equal(i, 0)), (x[i], True))))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n = Symbol(domain=Range(2, oo))
    x = Symbol(etype=dtype.integer, shape=(n,))
    Eq << apply(x)

    w = Eq[0].lhs.base
    Eq << Discrete.Indexed.eq.Piece.swap1.apply(x, w)

    i, j = Eq[-1].rhs.args[0][1].args
    Eq << Eq[-1].apply(Algebra.Cond.to.All.restrict, (i,), (j,))

    _i = i.unbounded
    Eq << Eq[-1].this.find(Lamda).limits_subs(i, _i)

    Eq << Algebra.Eq.to.Eq.Lamda.apply(Eq[-1], (_i, 0, n), simplify=False)


if __name__ == '__main__':
    run()
# created on 2020-09-12
