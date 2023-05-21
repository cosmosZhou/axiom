from util import *


@apply
def apply(eq, infer, eq_piece):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    (L, i, j), ecs = eq_piece.of(Equal[Indexed, Piecewise])
    return Element(L[1, 0], S.Complexes), Equal(A[1, 0], L[0, 0] * L[1, 0]), \
        Element(L[1, 1], Interval(0, oo, left_open=True)), Equal(A[1, 1], L[1, 1] ** 2 + L[1, 0] * ~L[1, 0])

@prove
def prove(Eq):
    from axiom import discrete, sets, algebra

    n = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    *Eq[-3:], (Eq.L10_is_complex, Eq.A10_def, Eq.L11_is_positive, Eq.A11_def) = apply(Equal(~A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], i > j), (sqrt(A[i, j] - L[i, :j] @ ~L[j, :j]), Equal(i, j)), (0, True))))

    Eq.L00_is_positive, Eq.A00_def = discrete.eq_transpose.all_gt_zero.eq_piece.imply.et.L00.apply(*Eq[:3])

    Eq << Element(A[1, 0], S.Complexes, plausible=True)

    Eq << sets.is_complex.is_positive.imply.is_complex.apply(Eq[-1], Eq.L00_is_positive)

    Eq << Eq[2].subs(i, 1).subs(j, 0).reversed

    Eq <<= Eq[-2].subs(Eq[-1]), Eq[-1] * Eq.L00_is_positive.lhs

    

    

    ξ = Symbol(r'{\color{red} {ξ}}', complex=True)
    Eq << Eq[1].subs(x, Lamda[i:n](Piecewise((ξ, Equal(i, 0)), (1, Equal(i, 1)), (0, True))))

    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.any.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.cond.subs, i, 1)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].subs(Eq[0][0, 1].reversed)

    Eq << Eq[-1].subs(Eq.A00_def, Eq.A10_def)

    Eq << sets.is_positive.imply.is_positive.square.apply(Eq.L00_is_positive)

    Eq << sets.is_nonzero.imply.eq.square_completing.apply(Eq[-1], Eq[-2].lhs, simplify=None)

    Eq << algebra.eq.gt.imply.gt.transit.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].subs(ξ, -Eq[-1].find(Indexed ** 2 * Add * Add).find(Mul))

    Eq << sets.is_real.imply.eq.conj.apply(Eq.L00_is_positive)

    Eq.gt_zero = Eq[-2].subs(Eq[-1])

    Eq << sets.is_complex.imply.is_nonnegative.mul.conj.apply(Eq.L10_is_complex)

    Eq << Element(A[1, 1], S.Complexes, plausible=True)

    Eq << sets.is_complex.is_complex.imply.is_complex.sub.apply(Eq[-1], Eq[-2])

    Eq << sets.gt_zero.is_complex.imply.is_positive.apply(Eq.gt_zero, Eq[-1])

    Eq << sets.is_positive.imply.is_positive.sqrt.apply(Eq[-1])

    Eq << Eq[2].subs(i, 1).subs(j, 1).this.find(MatMul).apply(discrete.matmul.to.sum).reversed
    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1] ** 2

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    
    


if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-05-03
