from util import *


@apply
def apply(eq_xy, eq_ab, i=None):
    (x, w), y = eq_xy.of(Equal[MatMul])
    (a, _w), b = eq_ab.of(Equal[MatMul])
    assert w == _w
    [n] = x.shape
    [__n] = a.shape
    _n, _i, _j = w.of(Swap)
    assert n == _n == __n
    assert _i >= 0 and _i < n
    assert _j >= 0 and _j < n
    if i is None:
        i = eq_xy.generate_var(eq_ab.free_symbols, integer=True, var='i')

    return Equal(Sum[i:n](x[i] * a[i]), Sum[i:n](y[i] * b[i]))


@prove
def prove(Eq):
    from axiom import discrete

    n = Symbol.n(integer=True, positive=True)
    x = Symbol.x(shape=(n,), real=True, given=True)
    y = Symbol.y(shape=(n,), real=True, given=True)
    a = Symbol.a(shape=(n,), real=True, given=True)
    b = Symbol.b(shape=(n,), real=True, given=True)
    i = Symbol.i(domain=Range(0, n))
    j = Symbol.j(domain=Range(0, n))
    Eq << apply(Equal(x @ Swap(n, i, j), y), Equal(a @ Swap(n, i, j), b))

    _i = Eq[-1].lhs.variable
    Eq << Eq[0][_i].reversed

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[1][_i].reversed

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1] * Eq[-3]

    Eq << Eq[2].subs(Eq[-1])

    

    

    

    

    

    

    

    


if __name__ == '__main__':
    run()