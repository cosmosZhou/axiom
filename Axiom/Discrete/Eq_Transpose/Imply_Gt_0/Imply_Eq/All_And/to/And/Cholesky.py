from util import *


@apply
def apply(eq, infer, eq_piece, All_And):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[x @ A @ x] = infer.of(Imply[Unequal[0], Expr > 0])
    (j, i), ((L, S[i], S[j]), (sub, S[L[j, j]])) = \
    eq_piece.of(Less >> Equal[Indexed, Expr / Expr])

    S[A[i, j]], (S[L[i, :j]], S[L[j, :j]]) = sub.of(Expr - Expr @ Expr)

    (S[Equal(A[i, i], Norm(L[i,:i + 1]) ** 2)], S[Element(L[i, i], Interval.open(0, oo))], S[All[j:i](Equal(A[i, j], L[i, :j + 1] @ L[j, :j + 1]) & Element(L[i, j], Reals))]), (S[i], S[0], t) = \
    All_And.of(All[And])

    return A[t, t] > Norm(L[t, :t]) ** 2, All[j:t](Equal(A[t, j], L[t, :j + 1] @ L[j, :j + 1]) & Element(L[t, j], Reals))

@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(3, n))
    Eq << apply(Equal(A.T, A),
        Imply(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0),
        Imply(j < i, Equal(L[i, j], (A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j])),
        All[i:t](And(
            Element(L[i, i], Interval.open(0, oo)),
            Equal(A[i, i], Norm(L[i,:i + 1]) ** 2),
            All[j:i](And(
                Element(L[i, j], Reals),
                Equal(A[i, j], L[i,:j + 1] @ L[j,:j + 1]))))))

    Eq << Algebra.All_And.to.And.All.apply(Eq[3])

    Eq.Aii_def, Eq.Lii_is_positive = Algebra.All_And.to.And.All.apply(Eq[-2])

    Eq.Aij_def, Eq.Lij_is_complex = Algebra.All_And.to.And.All.apply(Eq[-1])

    Eq << Algebra.All.All.to.All.And.apply(Eq.Lii_is_positive, Eq.Lij_is_complex)

    Eq << Eq[2].subs(i, t).subs(j, i)

    Eq << Algebra.Imply.to.All.single_variable.apply(Eq[-1], i)

    Eq << Algebra.All.All.to.All.And.apply(Eq[-1], Eq[-3])

    Eq << Discrete.All_And.to.All.And.Cholesky.real.apply(Eq[-1])

    Eq << Eq[1].subs(x, BlockMatrix(x[:t], 1, ZeroMatrix(n - t - 1)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.of.Any.Ne)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.of.Cond.subs, i, t)

    Eq << Eq[-1].this.lhs.args[:2].apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul.eq.Add)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)

    Eq << Eq[-1].this.find(Sum + Sum).args[1:3].apply(Algebra.Add.eq.Sum)

    Eq << Eq[-1].subs(Eq[0][i, t].reversed)

    Eq << Eq[-1].this.find(Sum[~Mul]).apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.find(Add[~Sum]).apply(Algebra.Sum.eq.Add.split.limits)

    Eq << Eq[-1].this.lhs.args[1:4:2].apply(Algebra.Add.eq.Sum)

    # converting A[j, i] to ~A[i, j] if j < i
    Eq << Eq[-1].subs(Eq[0][j, i].reversed)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Algebra.All_And.to.All.apply(Eq[5]).limits_subs(j, i)

    # converting all A expression to L expression: A[i, j] = L[i, j] + .... if i < j
    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq[-1], Eq[-2])

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq.Aii_def, Eq[-1])

    Eq << Eq.Aij_def.this.apply(Algebra.All.limits.swap.intlimit)

    Eq << Algebra.All_Eq.Cond.to.All.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.find(Mul[~Sum]).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Indexed * ~Sum).apply(Discrete.Sum.eq.Dot, simplify=1)

    Eq << Eq[-1].this.lhs.find(Sum[Mul]).limits_subs(j, i, simplify=None)

    Eq << Eq[-1].this.lhs.args[1:].apply(Algebra.Add.eq.Sum)

    Eq << Eq[-1].this.find(Sum).expr.args[1:].apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.find(MatMul + MatMul).apply(Discrete.Add.eq.Dot)

    Eq << Eq[-1].this.find(MatMul + Sliced).apply(Discrete.Add.eq.Dot.Block)

    Eq << Discrete.All_is_positive.Gt_0.to.Gt_0.Cholesky.real.apply(Eq.Lii_is_positive, Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-06-29