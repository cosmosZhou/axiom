from util import *


@apply
def apply(x, i=None, j=None, w=None):
    n = x.shape[0]
    if i is None:
        i = Symbol(domain=Range(n))

    if j is None:
        j = Symbol(domain=Range(n))

    if w is None:
        w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))

    return Equal(w[i, j] @ w[i, j] @ x, x)


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n = Symbol(domain=Range(2, oo))
    x = Symbol(shape=(n,), real=True)
    Eq << apply(x)

    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    Eq << (w[i, j] @ x).this.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Lamda)

    Eq << (w[i, j] @ Eq[-1]).this.rhs.subs(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.rhs.expr.args[-1].expr.apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.rhs().expr.simplify()

    k = Eq[-1].rhs.variable
    Eq << Eq[-1].this.rhs.expr.simplify(wrt=k)


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2020-11-14
