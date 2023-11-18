from util import *


@apply
def apply(given):
    (p_polynomial, *x), (S[p_polynomial], *y) = given.of(Equal[MatMul[2]])
    x = MatMul(*x)
    y = MatMul(*y)
    from axiom.discrete.eq_matmul.imply.eq.vector.independence.st.matmul import extract
    return Equal(*extract(p_polynomial, x, y))

@prove
def prove(Eq):
    from axiom import algebra, discrete

    p = Symbol(complex=True, zero=False)
    m, n, k = Symbol(positive=True, integer=True)
    x, y = Symbol(shape=(n, m), given=True, complex=True)
    Eq << apply(Equal(p ** Lamda[k:n](k) @ x, p ** Lamda[k:n](k) @ y))

    Eq << Eq[0].this.find(Pow[Lamda]).apply(algebra.expr.to.lamda, k)

    Eq << Eq[-1].this.find(Pow[Lamda]).apply(algebra.expr.to.lamda, k)

    Eq << discrete.eq_matmul.imply.eq.matrix.independence.st.matmul.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-08
# updated on 2023-04-09
