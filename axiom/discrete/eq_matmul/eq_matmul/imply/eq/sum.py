from util import *


@apply
def apply(eq_xy, eq_ab, i=None):
    (x, w), y = eq_xy.of(Equal[MatMul])
    (a, S[w]), b = eq_ab.of(Equal[MatMul])
    
    [n] = x.shape
    [S[n]] = a.shape
    _i, _j = w.of(SwapMatrix)
    assert _i >= 0 and _i < n
    assert _j >= 0 and _j < n
    if i is None:
        i = eq_xy.generate_var(eq_ab.free_symbols, integer=True, var='i')

    return Equal(Sum[i:n](x[i] * a[i]), Sum[i:n](y[i] * b[i]))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol(integer=True, positive=True)
    x, y, a, b = Symbol(shape=(n,), real=True, given=True)
    i, j = Symbol(domain=Range(n))
    Eq << apply(Equal(x @ SwapMatrix(n, i, j), y), Equal(a @ SwapMatrix(n, i, j), b))

    _i = Eq[-1].lhs.variable
    Eq << Eq[0][_i].reversed

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[1][_i].reversed

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1] * Eq[-3]

    Eq << Eq[2].subs(Eq[-1])


















if __name__ == '__main__':
    run()
# created on 2019-11-13
