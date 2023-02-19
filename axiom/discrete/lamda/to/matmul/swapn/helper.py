from util import *


@apply
def apply(x, d, w=None):
    n = x.shape[0]
    m = d.shape[0]
    assert m.is_integer and m.is_finite
    i, j, k = Symbol(integer=True)

    if w is None:
        w = Symbol(Lamda[j, i](SwapMatrix(n, i, j)))
    else:
        assert len(w.shape) == 4 and all(s == n for s in w.shape)
        assert w[i, j].is_SwapMatrix or w[i, j].definition.is_SwapMatrix

    multiplier = MatProduct[i:m](w[i, d[i]])
    return Equal(Lamda[k:n](x[(Lamda[k:n](k) @ multiplier)[k]]), x @ multiplier)


@prove(proved=False)
def prove(Eq):
    from axiom import discrete, algebra
    n = Symbol(domain=Range(2, oo))
    assert n.is_integer

    m = Symbol(domain=Range(1, oo), given=False)
    assert m.is_integer

    x = Symbol(complex=True, shape=(n,))
    d = Symbol(integer=True, shape=(oo,))

    Eq << apply(x, d[:m])

    k = Eq[-1].lhs.variable
    i, j = Eq[0].lhs.indices
    w = Eq[0].lhs.base
    multiplier = MatProduct[i:m](w[i, d[i]])
    Eq.hypothesis = Equal(x[(Lamda[k:n](k) @ multiplier)[k]], (x @ multiplier)[k], plausible=True)

    Eq.initial = Eq.hypothesis.subs(m, 1)

    d = Eq[1].rhs.args[1].expr.indices[1].base
    Eq << discrete.lamda_indexed.to.matmul.swap.apply(x, w, left=False, reference=None).subs(i, 0).subs(j, d[0])

    Eq.induct = Eq.hypothesis.subs(m, m + 1)

    Eq << discrete.indexed.to.matmul.swap.apply(x, Lamda[k](Eq[1].lhs.expr.indices[0]).simplify(), w)

    Eq << Eq[-1].subs(i, m).subs(j, d[m])

    Eq << algebra.eq.imply.eq.lamda.apply(Eq.hypothesis, (k, 0, n))

    Eq << Eq[-1].subs(Eq[1])

    Eq << Infer(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << algebra.cond.infer.imply.cond.induct.apply(Eq.initial, Eq[-1], n=m, start=1)


if __name__ == '__main__':
    run()
# created on 2020-09-02
