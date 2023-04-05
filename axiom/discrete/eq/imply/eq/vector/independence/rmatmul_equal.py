from util import *


@apply
def apply(given):
    (x, p_polynomial), (y, S[p_polynomial]) = given.of(Equal[MatMul[2]])

    assert p_polynomial.shape == x.shape == y.shape
    (b, e), (k, *ab) = p_polynomial.of(Lamda[Pow])
#     n = p_polynomial.shape[0]
    assert not b.has(k)
    assert e.as_poly(k).degree() == 1

    return Equal(x, y)


@prove
def prove(Eq):
    from axiom import discrete
    p = Symbol(complex=True)
    n, k = Symbol(domain=Range(1, oo))
    x, y = Symbol(shape=(n,), given=True, complex=True)

    Eq << apply(Equal(x @ Lamda[k:n](p ** k), y @ Lamda[k:n](p ** k)))

    Eq << discrete.matmul.cosine_similarity.apply(*Eq[0].lhs.args)

    Eq << discrete.matmul.cosine_similarity.apply(*Eq[0].rhs.args)

    Eq << Eq[0].subs(Eq[-1], Eq[-2])

    Eq << discrete.eq.imply.eq.vector.independence.matmul_equal.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2020-08-22
