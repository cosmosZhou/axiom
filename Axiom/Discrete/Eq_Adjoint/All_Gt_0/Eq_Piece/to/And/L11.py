from util import *


@apply
def apply(eq, infer, eq_piece):
    from Axiom.Discrete.Eq_Adjoint.Imply_Gt_0.Eq_Piece.to.All.And.Cholesky import extract
    A, L, x, i, j = extract(eq, infer, eq_piece)
    return Element(L[1, 0], S.Complexes), Equal(A[1, 0], L[0, 0] * L[1, 0]), \
        Element(L[1, 1], Interval.open(0, oo)), Equal(A[1, 1], Norm(L[1, :2]) ** 2)

@prove
def prove(Eq):
    from Axiom import Discrete, Sets, Algebra

    n = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    *Eq[-3:], (Eq.L10_is_complex, Eq.A10_def, Eq.L11_is_positive, Eq.A11_def) = apply(Equal(~A.T, A),
               Imply(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

    Eq.L00_is_positive, Eq.A00_def = Discrete.Eq_Adjoint.All_Gt_0.Eq_Piece.to.And.L00.apply(*Eq[:3])

    Eq << Element(A[1, 0], S.Complexes, plausible=True)

    Eq << Sets.is_complex.is_positive.to.is_complex.apply(Eq[-1], Eq.L00_is_positive)

    Eq << Eq[2].subs(i, 1).subs(j, 0).reversed

    Eq <<= Eq[-2].subs(Eq[-1]), Eq[-1] * Eq.L00_is_positive.lhs

    ξ = Symbol(r'{\color{red} {ξ}}', complex=True)
    Eq << Eq[1].subs(x, Lamda[i:n](Piecewise((ξ, Equal(i, 0)), (1, Equal(i, 1)), (0, True))))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.of.Any.Ne)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.of.Cond.subs, i, 1)

    Eq << Eq[-1].this.lhs.args[:2].apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[-1].subs(Eq[0][0, 1].reversed)

    Eq << Eq[-1].subs(Eq.A00_def, Eq.A10_def)

    Eq << Sets.is_positive.to.is_positive.Square.apply(Eq.L00_is_positive)

    Eq << Sets.is_nonzero.to.Eq.Conj.square_completing.apply(Eq[-1], Eq[-2].lhs, simplify=None)

    Eq << Algebra.Eq.Gt.to.Gt.trans.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].subs(ξ, -Eq[-1].find(Indexed ** 2 * Add * Add).find(Mul))

    Eq << Sets.is_real.to.Eq.Conj.apply(Eq.L00_is_positive)

    Eq.gt_zero = Eq[-2].subs(Eq[-1])

    Eq << Sets.is_complex.to.is_nonnegative.Mul.Conj.apply(Eq.L10_is_complex)

    Eq << Element(A[1, 1], S.Complexes, plausible=True)

    Eq << Sets.is_complex.is_complex.to.is_complex.Sub.apply(Eq[-1], Eq[-2])

    Eq << Sets.Gt_0.is_complex.to.is_positive.apply(Eq.gt_zero, Eq[-1])

    Eq << Sets.is_positive.to.is_positive.Sqrt.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul).args[1:].apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[2].subs(i, 1).subs(j, 1).reversed

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1] ** 2

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq.A11_def.this.find(Norm).apply(Algebra.Norm.eq.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.doit)

    Eq << Sets.is_real.to.Eq.Square.Abs.apply(Eq.L11_is_positive)

    Eq << Eq[-2].subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-06-28