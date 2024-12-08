from util import *


@apply
def apply(eq, infer, eq_piece):
    from Axiom.Discrete.Eq_Adjoint.Imply_Gt_0.Eq_Piece.to.All.And.Cholesky import extract
    A, L, x, i, j = extract(eq, infer, eq_piece)
    return Element(L[0, 0], Interval.open(0, oo)), Equal(A[0, 0], L[0, 0] ** 2)

@prove
def prove(Eq):
    from Axiom import Algebra, Sets

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    *Eq[-3:], (Eq.L00_is_positive, Eq.A00_def) = apply(Equal(~A.T, A),
               Imply(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

    Eq << Algebra.All_Gt_0.to.Gt_0.positive_definite.apply(Eq[1], i)

    Eq << Eq[-1].subs(i, 0)

    Eq << Algebra.Gt_0.to.Gt_0.Sqrt.apply(Eq[-1])

    Eq << Sets.Gt_0.to.is_positive.apply(Eq[-1], simplify=None)

    Eq << Eq[2].subs(i, 0).subs(j, 0)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].reversed ** 2





if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-06-28
