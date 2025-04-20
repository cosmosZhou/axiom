from util import *


@apply
def apply(given):
    (p_polynomial, *x), (S[p_polynomial], *y) = given.of(Equal[MatMul[2]])
    x = MatMul(*x)
    y = MatMul(*y)
    from Axiom.Discrete.Eq.of.EqDotSLamda_Pow.independence.vector import extract
    return Equal(*extract(p_polynomial, x, y))


@prove
def prove(Eq):
    from Axiom import Discrete

    p = Symbol(complex=True, zero=False)
    m, n, k = Symbol(positive=True, integer=True)
    x, y = Symbol(shape=(n, m), given=True, complex=True)
    given = Equal(Lamda[k:n](p ** k) @ x, Lamda[k:n](p ** k) @ y)
    Eq << apply(given)

    Eq << Eq[0].T

    Eq << Discrete.Eq.of.EqDotS_Lamda_Pow.independence.matrix.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-10-30
# updated on 2023-04-08
