from util import *


@apply
def apply(eq, infer, eq_piece, t):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    (L, i, j), ecs = eq_piece.of(Equal[Indexed, Piecewise])
    return All[i:t](And(
        Element(L[i, i], Interval(0, oo, left_open=True)),
        Equal(A[i, i], L[i, i] ** 2 + L[i,:i] @ ~ L[i,:i]),
        All[j:i](And(
            Element(L[i, j], S.Complexes),
            Equal(A[i, j], L[i, j] * L[j, j] + L[i,:j] @ ~ L[j,:j])))))

@prove
def prove(Eq):
    from axiom import algebra, discrete, sets

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(3, n), given=False)
    *Eq[-3:], Eq.hypothesis = apply(Equal(~A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], i > j), (sqrt(A[i, j] - L[i, :j] @ ~L[j, :j]), Equal(i, j)), (0, True))), t)

    Eq << algebra.all_gt_zero.imply.gt_zero.positive_definite.apply(Eq[1], i)

    Eq.L00_is_positive, Eq.A00_def = discrete.eq_transpose.all_gt_zero.eq_piece.imply.et.L00.apply(*Eq[:3])

    Eq.L10_is_complex, Eq.A10_def, Eq.L11_is_positive, Eq.A11_def = discrete.eq_transpose.all_gt_zero.eq_piece.imply.et.L11.apply(*Eq[:3])

    Eq.L20_is_complex, Eq.A20_def, Eq.L21_is_complex, Eq.A21_def, Eq.L22_is_positive, Eq.A22_def = discrete.eq_transpose.all_gt_zero.eq_piece.imply.et.L22.apply(*Eq[:3])

    Eq.L30_is_complex, Eq.A30_def, Eq.L31_is_complex, Eq.A31_def, Eq.L32_is_complex, Eq.A32_def, Eq.L33_is_positive, Eq.A33_def = discrete.eq_transpose.all_gt_zero.eq_piece.imply.et.L33.apply(*Eq[:3])

    Eq << algebra.all_et.imply.et.all.apply(Eq.hypothesis)

    Eq.Aii_def, Eq.Lii_is_positive = algebra.all_et.imply.et.all.apply(Eq[-2])

    Eq.Aij_def, Eq.Lij_is_complex = algebra.all_et.imply.et.all.apply(Eq[-1])

    Eq << Eq.hypothesis.subs(t, t + 1)

    Eq.Att_def, Eq.Ltt_is_positive, Eq.Atj_def_and_Ltj_is_complex, Eq[-1] = algebra.all.given.et.all.split.apply(Eq[-1], cond=Equal(i, t))

    k = Symbol(domain=Range(t), given=False)
    #apply the second mathematical induction on k
    Eq.tk_hypothesis = All[j:k](Eq.Atj_def_and_Ltj_is_complex.expr, plausible=True)

    Eq.tk_induct = Eq.tk_hypothesis.subs(k, k + 1)

    Eq << algebra.all.given.et.all.split.apply(Eq.tk_induct, cond=Equal(j, k))

    Eq << Eq.Lij_is_complex.this.expr.apply(sets.is_complex.imply.is_complex.conj)

    Eq << algebra.all.imply.cond.subs.apply(Eq[-1], i, k)

    Eq << algebra.all_et.imply.et.all.apply(Eq.tk_hypothesis)

    Eq <<= Eq[-1] & Eq[-3]

    Eq << Eq[-1].this.expr.apply(sets.is_complex.is_complex.imply.is_complex)

    Eq << sets.all_is_complex.imply.is_complex.sum.apply(Eq[-1])

    Eq << Element(A[t, k], S.Complexes, plausible=True)

    Eq << sets.is_complex.is_complex.imply.is_complex.sub.apply(Eq[-1], Eq[-2])

    Eq.Lkk_is_positive = algebra.all.imply.cond.subs.apply(Eq.Lii_is_positive, i, k)

    Eq << sets.is_complex.is_positive.imply.is_complex.apply(Eq[-1], Eq.Lkk_is_positive)

    Eq << Eq[2].subs(i, t).subs(j, k).this.find(MatMul).apply(discrete.matmul.to.sum).reversed

    Eq <<= Eq[-2].subs(Eq[-1]), Eq[-1] * Eq.Lkk_is_positive.lhs

    Eq <<= algebra.et.given.et.apply(Eq[-2]), Eq[-1] - Add(*Eq[-1].lhs.args[1:])

    Eq << sets.is_positive.imply.ne_zero.apply(Eq.Lkk_is_positive)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul)

    Eq << Infer(Eq.tk_hypothesis, Eq.tk_induct, plausible=True)

    Eq << algebra.infer.imply.cond.induct.apply(Eq[-1], k, 0)

    Eq << algebra.cond.imply.all.apply(Eq.tk_induct, k)

    Eq << algebra.all.imply.cond.subs.apply(Eq[-1], Eq[-1].variables[-1], t - 1)

    Eq << Infer(Eq.hypothesis, Eq[7], plausible=True)

    #this must be True~
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << Eq[1].subs(x, BlockMatrix(ξ[:t], 1, ZeroMatrix(n - t - 1)))

    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.any.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.cond.subs, i, t)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)

    Eq << Eq[-1].this.find(Sum + Sum).args[1:3].apply(algebra.add.to.sum)

    Eq << Eq[-1].subs(Eq[0][i, t].reversed)

    Eq << Eq[-1].this.find(Sum[~Mul]).apply(algebra.mul.to.sum)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add.split.limits)

    Eq << Eq[-1].this.find(Sum + Sum).args[1:3].apply(algebra.add.to.sum)

    #converting A[j, i] to ~A[i, j] if j < i
    Eq << Eq[-1].subs(Eq[0][j, i].reversed)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.limits.swap.intlimit)

    #converting all A expression to L expression: A[i, j] = L[i, j] + .... if i < j
    Eq << algebra.all_et.imply.all.apply(Eq.Atj_def_and_Ltj_is_complex).limits_subs(j, i)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[-2])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.Aii_def, Eq[-1])

    Eq << Eq.Aij_def.this.apply(algebra.all.limits.swap.intlimit)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[-2])

    k = Symbol(domain=Range(0, t - 1), given=False)
    Eq.square_completing_hypothesis = Greater(A[t, t] + Sum[i:k:t](Eq[-1].find(Sum).expr) + Sum[i:j + 1:t, j:k:t](Eq[-1].find(Sum[2]).expr) - Sum[j:k]((L[t, j] + Sum[i:k:t](L[i, j] * ~ξ[i])) * (~L[t, j] + Sum[i:k:t](~L[i, j] * ξ[i]))),  0, plausible=True)

    Eq << Eq.square_completing_hypothesis.subs(k, 0)

    Eq << Eq.square_completing_hypothesis.subs(k, k + 1)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Add * Add).find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.find(Add * Add).find(Sum).apply(algebra.sum.to.add.shift)

    Eq << Eq[-1].this.find(Add * Add).apply(algebra.mul.to.add, deep=True)

    Eq << Eq[-1].this.find(Sum[Add[Mul[Sum]]]).expr.apply(algebra.add.collect, ξ[k + 1])

    Eq << Eq[-1].this.find(Sum[Add[Mul[Sum]]]).expr.apply(algebra.add.collect, ~ξ[k + 1])

    Eq << Eq[-1].this.find(Sum[Add[Mul[Sum]]]).expr.apply(algebra.add.collect, L[t, j])

    Eq << Eq[-1].this.find(Sum[Add[Mul[Sum]]]).expr.apply(algebra.add.collect)

    Eq << Eq[-1].this.find(Sum[Add[Mul[Sum]]]).expr.apply(algebra.add.collect)

    Eq << Eq[-1].this.find(Sum[Add[Add * Add]]).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(Indexed * ~Sum[Add[Mul[Sum]]]).apply(algebra.sum.to.add)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum, i)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum, i)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum, j)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum, j)

    #now start the square completing process:
    Eq.Lk1_is_positive = algebra.all.imply.cond.subs.apply(Eq.Lii_is_positive, i, k + 1)

    Eq << sets.is_positive.imply.is_positive.square.apply(Eq.Lk1_is_positive)

    Eq << sets.is_nonzero.imply.eq.square_completing.apply(Eq[-1], Add(*[arg for arg in Eq[-2].lhs.args if arg._has(ξ[k + 1])]), ξ[k + 1], simplify=None)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].find(Indexed ** 2 * Add * Add).find(Mul)

    Eq << Eq[-1].subs(ξ[k + 1], -Eq[-1].find(Indexed ** 2 * Add * Add).find(Mul))

    Eq << sets.is_real.imply.eq.conj.apply(Eq.Lk1_is_positive)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.lhs.find(~Add * Add)

    return
    Eq << Eq[-1].this.find((~Add) * Add * Indexed ** -2).apply(algebra.add.to.mul)
    
    


if __name__ == '__main__':
    run()
# created on 2023-05-01
from . import real
# updated on 2023-05-21
