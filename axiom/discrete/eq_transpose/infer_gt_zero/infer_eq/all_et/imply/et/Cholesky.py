from util import *


@apply
def apply(eq, infer, eq_piece, all_et):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[x @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    (j, i), ((L, S[i], S[j]), (sub, S[L[j, j]])) = \
    eq_piece.of(Less >> Equal[Indexed, Expr / Expr])

    S[A[i, j]], (S[L[i, :j]], S[L[j, :j]]) = sub.of(Expr - Expr @ Expr)

    (S[Equal(A[i, i], Norm(L[i,:i + 1]) ** 2)], S[Element(L[i, i], Interval.open(0, oo))], S[All[j:i](Equal(A[i, j], L[i, :j + 1] @ L[j, :j + 1]) & Element(L[i, j], Reals))]), (S[i], S[0], t) = \
    all_et.of(All[And])

    return A[t, t] > Norm(L[t, :t]) ** 2, All[j:t](Equal(A[t, j], L[t, :j + 1] @ L[j, :j + 1]) & Element(L[t, j], Reals))

@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(3, n))
    Eq << apply(Equal(A.T, A),
        Infer(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0),
        Infer(j < i, Equal(L[i, j], (A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j])),
        All[i:t](And(
            Element(L[i, i], Interval.open(0, oo)),
            Equal(A[i, i], Norm(L[i,:i + 1]) ** 2),
            All[j:i](And(
                Element(L[i, j], Reals),
                Equal(A[i, j], L[i,:j + 1] @ L[j,:j + 1]))))))

    Eq << algebra.all_et.imply.et.all.apply(Eq[3])

    Eq.Aii_def, Eq.Lii_is_positive = algebra.all_et.imply.et.all.apply(Eq[-2])

    Eq.Aij_def, Eq.Lij_is_complex = algebra.all_et.imply.et.all.apply(Eq[-1])

    Eq << algebra.all.all.imply.all.et.apply(Eq.Lii_is_positive, Eq.Lij_is_complex)

    Eq << Eq[2].subs(i, t).subs(j, i)

    Eq << algebra.infer.imply.all.single_variable.apply(Eq[-1], i)

    Eq << algebra.all.all.imply.all.et.apply(Eq[-1], Eq[-3])

    Eq << discrete.all_et.imply.all.et.Cholesky.real.apply(Eq[-1])

    Eq << Eq[1].subs(x, BlockMatrix(x[:t], 1, ZeroMatrix(n - t - 1)))

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

    Eq << Eq[-1].this.find(Add[~Sum]).apply(algebra.sum.to.add.split.limits)

    Eq << Eq[-1].this.lhs.args[1:4:2].apply(algebra.add.to.sum)

    #converting A[j, i] to ~A[i, j] if j < i
    Eq << Eq[-1].subs(Eq[0][j, i].reversed)

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.limits.swap.intlimit)

    Eq << algebra.all_et.imply.all.apply(Eq[5]).limits_subs(j, i)

    #converting all A expression to L expression: A[i, j] = L[i, j] + .... if i < j
    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[-2])

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq.Aii_def, Eq[-1])

    Eq << Eq.Aij_def.this.apply(algebra.all.limits.swap.intlimit)

    Eq << algebra.all_eq.cond.imply.all.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.find(Mul[~Sum]).apply(algebra.sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Indexed * ~Sum).apply(discrete.sum.to.matmul, simplify=1)

    Eq << Eq[-1].this.lhs.find(Sum[Mul]).limits_subs(j, i, simplify=None)

    Eq << Eq[-1].this.lhs.args[1:].apply(algebra.add.to.sum)

    Eq << Eq[-1].this.find(Sum).expr.args[1:].apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(MatMul + MatMul).apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.find(MatMul + Sliced).apply(discrete.add.to.matmul.block)

    Eq << discrete.all_is_positive.gt_zero.imply.gt_zero.Cholesky.real.apply(Eq.Lii_is_positive, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-06-29
