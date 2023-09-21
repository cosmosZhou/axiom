from util import *


@apply
def apply(given):
    (*x, p_polynomial), (*y, S[p_polynomial]) = given.of(Equal[MatMul[2]])
    x = MatMul(*x)
    y = MatMul(*y)

    from axiom.discrete.eq_matmul.imply.eq.vector.independence.st.matmul import extract
    x, y = extract(p_polynomial, x, y)

    if given.is_Exists:
        return Any(Equal(x, y), (x,), (y,))
    else:
        return Equal(x, y)


@prove
def prove(Eq):
    from axiom import algebra, discrete

    p = Symbol(complex=True, zero=False)
    m, n, k = Symbol(domain=Range(1, oo))
    x, y = Symbol(shape=(m, n))
    Eq << apply(Equal(x @ Lamda[k:n](p ** k), y @ Lamda[k:n](p ** k)))

    i = Symbol(domain=Range(m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[1], i)

    Eq << Eq[0][i]

    Eq << discrete.eq_matmul.imply.eq.vector.independence.st.rmatmul.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2020-08-22
# updated on 2023-04-08
