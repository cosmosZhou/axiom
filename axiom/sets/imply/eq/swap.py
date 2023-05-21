from util import *


@apply
def apply(x, i=None, j=None):
    n, = x.shape

    assert x.dtype.is_set
    if i is None:
        i = Symbol(integer=True)

    if j is None:
        j = Symbol(integer=True)

    return Equal(swap[i, j](swap[i, j](x)), x)


def swap(p, *indices):
    n = p.shape[0]
    i, j = Symbol(integer=True)
    w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))

    [i], [j] = indices
    k = Symbol(integer=True)

#     d = w[i, j] @ Lamda[k:n](k)
    dk = Lamda[k:n](k) @ w[i, j, k]
    return Lamda[k:n](p[dk])
#     return Lamda[k:n](p[d[k]])


swap = Function(eval=swap)


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(positive=True, integer=True)
    x = Symbol(shape=(n,), etype=dtype.integer)
    Eq << apply(x)

    (i,), (j,) = Eq[0].lhs.limits
    Eq << Eq[-1].this.lhs.arg.defun()

    Eq << Eq[-1].this.lhs.defun()

    w = Eq[-1].lhs.expr.indices[0].args[1].base
    Eq << discrete.lamda_indexed.to.matmul.swap.apply(w[i, j], left=False, w=w, reference=False)

    k = Eq[-1].rhs.args[1].indices[-1]
    Eq << Eq[-2].lhs.expr.index.this.subs(Eq[-1])

    Eq << discrete.eq.imply.eq.matpow.to.identity.apply(w[i, j].this.definition)

    Eq << Eq[-1][k].T

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this(k).rhs.simplify()

    Eq << Eq[2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.simplify()

    


if __name__ == '__main__':
    run()
# https://docs.sympy.org/latest/modules/combinatorics/permutations.html
# created on 2021-03-30
# updated on 2023-05-21
