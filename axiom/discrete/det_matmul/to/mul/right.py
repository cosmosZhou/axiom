from util import *


@apply
def apply(self):
    A, (I0, I1) = self.of(Determinant[Expr @ BlockMatrix[BlockMatrix[1][ZeroMatrix, Expr], BlockMatrix[1][Expr, ZeroMatrix]]])
    assert I0.is_Identity
    assert I1.is_Identity

    return Equal(self, Det(A) * (-1) ** (I0.shape[-1] * I1.shape[-1]))


@prove(proved=False)
def prove(Eq):
    n, m = Symbol(integer=True, positive=True)
    A = Symbol(shape=(m + n, m + n), complex=True)
    Eq << apply(Determinant(A @ BlockMatrix([[ZeroMatrix(m, n), Identity(m)], [Identity(n), ZeroMatrix(n, m)]])))


if __name__ == '__main__':
    run()
# created on 2020-08-19
