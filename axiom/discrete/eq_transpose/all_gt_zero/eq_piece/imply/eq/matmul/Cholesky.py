from util import *


@apply
def apply(eq, infer, eq_piece):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[x @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    (L, i, j), ecs = eq_piece.of(Equal[Indexed, Piecewise])
    return Equal(A, L @ L.T)

@prove
def prove(Eq):
    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], i > j), (sqrt(A[i, j] - L[i, :j] @ ~L[j, :j]), Equal(i, j)), (0, True))))

    

    

    

    


if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-05-02
