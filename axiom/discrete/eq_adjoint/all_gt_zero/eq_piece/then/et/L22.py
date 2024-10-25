from util import *


@apply
def apply(eq, infer, eq_piece):
    from axiom.discrete.eq_adjoint.infer_gt_zero.eq_piece.then.all.et.Cholesky import extract
    A, L, x, i, j = extract(eq, infer, eq_piece)
    return Element(L[2, 0], S.Complexes), Equal(A[2, 0], L[0, 0] * L[2, 0]), \
        Element(L[2, 1], S.Complexes), Equal(A[2, 1], ~L[1, 0] * L[2, 0] + L[1, 1] * L[2, 1]), \
        Element(L[2, 2], Interval.open(0, oo)), Equal(A[2, 2], Norm(L[2, :3]) ** 2)

@prove
def prove(Eq):
    from axiom import discrete, sets, algebra

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    *Eq[-3:], (Eq.L20_is_complex, Eq.A20_def, Eq.L21_is_complex, Eq.A21_def, Eq.L22_is_positive, Eq.A22_def) = apply(Equal(~A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

    Eq.L00_is_positive, Eq.A00_def = discrete.eq_adjoint.all_gt_zero.eq_piece.then.et.L00.apply(*Eq[:3])

    Eq.L10_is_complex, Eq.A10_def, Eq.L11_is_positive, Eq.A11_def = discrete.eq_adjoint.all_gt_zero.eq_piece.then.et.L11.apply(*Eq[:3])

    Eq << Element(A[2, 0], S.Complexes, plausible=True)

    Eq << sets.is_complex.is_positive.then.is_complex.apply(Eq[-1], Eq.L00_is_positive)

    Eq << Eq[2].subs(i, 2).subs(j, 0).reversed

    Eq <<= Eq[-2].subs(Eq[-1]), Eq[-1] * Eq.L00_is_positive.lhs

    Eq << Element(A[2, 1], S.Complexes, plausible=True)

    Eq << sets.is_complex.then.is_complex.conj.apply(Eq.L10_is_complex)

    Eq << sets.is_complex.is_complex.then.is_complex.apply(Eq[-1], Eq.L20_is_complex)

    Eq << sets.is_complex.is_complex.then.is_complex.sub.apply(Eq[-3], Eq[-1])

    Eq << sets.is_complex.is_positive.then.is_complex.apply(Eq[-1], Eq.L11_is_positive)

    Eq << Eq[2].subs(i, 2).subs(j, 1).reversed

    Eq <<= Eq[-2].subs(Eq[-1]), Eq[-1] * Eq.L11_is_positive.lhs

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << Eq[1].subs(x, Lamda[i:n](Piecewise((ξ[0], Equal(i, 0)), (ξ[1], Equal(i, 1)), (1, Equal(i, 2)), (0, True))))

    Eq << Eq[-1].this.lhs.apply(algebra.ne.of.any.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.any.of.cond.subs, i, 2)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].subs(Eq[0][0, 1].reversed, Eq[0][0, 2].reversed, Eq[0][1, 2].reversed)

    Eq << Eq[-1].subs(Eq.A00_def, Eq.A10_def, Eq.A11_def, Eq.A20_def, Eq.A21_def)

    Eq << sets.is_positive.then.is_positive.square.apply(Eq.L00_is_positive)

    Eq << sets.is_nonzero.then.eq.conj.square_completing.apply(Eq[-1], Eq[-2].lhs, ξ[0], simplify=None)

    Eq << algebra.eq.gt.then.gt.trans.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].subs(ξ[0], -Eq[-1].find(Indexed ** 2 * Add * Add).find(Mul))

    Eq << sets.is_real.then.eq.conj.apply(Eq.L00_is_positive)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Add * ~Add).apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Add * ~Add).apply(algebra.add.to.mul)

    Eq << Eq[-1].find(Norm ** 2).this.base.apply(algebra.norm.to.sqrt).this.rhs.apply(algebra.sum.to.add.doit)

    Eq << Eq[-1].this.find(Abs ** 2).apply(algebra.square.abs.to.mul.conj)

    Eq << sets.is_positive.then.eq.abs.apply(Eq.L11_is_positive)

    Eq << Eq[-4].subs(*Eq[-2:])

    Eq << sets.is_positive.then.is_positive.square.apply(Eq.L11_is_positive)

    Eq << sets.is_nonzero.then.eq.conj.square_completing.apply(Eq[-1], Eq[-2].lhs, ξ[1], simplify=None)

    Eq << algebra.eq.gt.then.gt.trans.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].subs(ξ[1], -Eq[-1].find(Indexed ** 2 * Add * Add).find(Mul))

    Eq << sets.is_real.then.eq.conj.apply(Eq.L11_is_positive)

    Eq.gt_zero = Eq[-2].subs(Eq[-1])

    Eq << sets.is_complex.then.is_nonnegative.mul.conj.apply(Eq.L20_is_complex)

    Eq << sets.is_complex.then.is_nonnegative.mul.conj.apply(Eq.L21_is_complex)

    Eq << sets.is_nonnegative.is_nonnegative.then.is_nonnegative.add.apply(Eq[-1], Eq[-2])

    Eq << Element(A[2, 2], S.Complexes, plausible=True)

    Eq << sets.is_complex.is_complex.then.is_complex.sub.apply(Eq[-1], Eq[-2])

    Eq << sets.gt_zero.is_complex.then.is_positive.apply(Eq.gt_zero, Eq[-1])

    Eq << sets.is_positive.then.is_positive.sqrt.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul).args[1:].apply(algebra.mul.conj.to.square.abs)

    Eq << Eq[-1].this.find(Mul).args[1:].apply(algebra.mul.conj.to.square.abs)

    Eq << Eq[2].subs(i, 2).subs(j, 2).reversed

    Eq << Eq[-1].this.find(Norm).apply(algebra.norm.to.sqrt).this.find(Sum).apply(algebra.sum.to.add.doit)

    Eq << Eq[-3].subs(Eq[-1]), Eq[-1] ** 2

    Eq << Eq[-1] ** 2

    Eq << Eq[-1] - Add(*Eq[-1].lhs.args[1:])

    Eq << Eq.A22_def.this.find(Norm).apply(algebra.norm.to.sqrt)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.doit)

    Eq << sets.is_real.then.eq.square.abs.apply(Eq.L22_is_positive)

    Eq << Eq[-2].subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-05-02
# updated on 2023-06-28
