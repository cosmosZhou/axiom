from util import *


@apply
def apply(eq, infer, eq_piece):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    (L, i, j), ecs = eq_piece.of(Equal[Indexed, Piecewise])
    return Element(L[0, 0], Interval(0, oo, left_open=True)), Equal(A[0, 0], L[0, 0] ** 2)

@prove
def prove(Eq):
    from axiom import algebra, sets

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    *Eq[-3:], (Eq.L00_is_positive, Eq.A00_def) = apply(Equal(~A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], i > j), (sqrt(A[i, j] - L[i, :j] @ ~L[j, :j]), Equal(i, j)), (0, True))))

    Eq << algebra.all_gt_zero.imply.gt_zero.positive_definite.apply(Eq[1], i)

    Eq << Eq[-1].subs(i, 0)

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1])

    Eq << sets.gt_zero.imply.is_positive.apply(Eq[-1], simplify=None)

    Eq << Eq[2].subs(i, 0).subs(j, 0)

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].reversed ** 2
    
    


if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-05-03
