from util import *


@apply
def apply(self):
    from Axiom.Algebra.Sum.limits.swap.subs import rewrite
    return rewrite(All, self)


@prove
def prove(Eq):
    i, j, k = Symbol(integer=True)
    A = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)
    f = Function(integer=True)
    g = Symbol(shape=(oo, oo), bool=True)
    h = Symbol(shape=(oo,), bool=True)
    Eq << apply(All[i:f(j), j:A](h[i] & g[i, j]))

    Eq << Eq[-1].this.rhs.limits_subs(i, k)

    Eq << Eq[-1].this.lhs.limits_subs(j, k)

    Eq << Eq[-1].this.lhs.limits_subs(i, j)


if __name__ == '__main__':
    run()
# created on 2023-11-11
