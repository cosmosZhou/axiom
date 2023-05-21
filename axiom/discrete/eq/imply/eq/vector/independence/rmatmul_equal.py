from util import *


@apply
def apply(given):
    (x, p_polynomial), (y, S[p_polynomial]) = given.of(Equal[MatMul[2]])
    from axiom.discrete.eq.imply.eq.vector.independence.matmul_equal import extract
    return Equal(*extract(p_polynomial, x, y))


@prove
def prove(Eq):
    from axiom import discrete

    p = Symbol(complex=True, zero=False)
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
# updated on 2023-04-08
