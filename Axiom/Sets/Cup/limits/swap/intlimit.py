from util import *


@apply
def apply(self):
    from Axiom.Algebra.Sum.limits.swap.intlimit import limits_swap
    return Equal(self, limits_swap(Cup, self))


@prove
def prove(Eq):
    from Axiom import Sets
    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)

    f = Symbol(shape=(oo,), etype=dtype.real)
    g = Symbol(shape=(oo, oo), etype=dtype.real)


    Eq << apply(Cup[i:a + d:j + d, j:a + 1:n](f[i] & g[i, j]))

    Eq << Eq[0].this.lhs.apply(Sets.Cup.Piece)

    Eq << Eq[-1].this.lhs.expr.args[0].cond.apply(Sets.In.In.transform.i_Lt_j)

    Eq << Eq[-1].this.rhs.apply(Sets.Cup.Piece)

    Eq << Eq[-1].this.rhs.apply(Sets.Cup.limits.swap)


if __name__ == '__main__':
    run()

# created on 2021-02-11