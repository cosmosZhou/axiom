from util import *


@apply
def apply(given):
    (p_polynomial, *x), (S[p_polynomial], *y) = given.of(Equal[MatMul[2]])
    x = MatMul(*x)
    y = MatMul(*y)
    assert x.shape == y.shape
    assert len(p_polynomial.shape) == 1
    assert len(x.shape) == 2

    (b, e), (k, *ab) = p_polynomial.of(Lamda[Pow])
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1
    return Equal(x, y)


@prove
def prove(Eq):
    from axiom import discrete
    p = Symbol(complex=True)
    m, n, k = Symbol(positive=True, integer=True)
    x, y = Symbol(shape=(n, m), given=True, complex=True)

    given = Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y)

    Eq << apply(given)

    Eq << Eq[0].T

    Eq << discrete.eq.imply.eq.matrix.independence.rmatmul_equal.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-10-30
