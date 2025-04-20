from util import *


@apply
def apply(eq, infer, eq_piece, All_And):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Imply[Unequal[0], Expr > 0])
    (j, i), ((L, S[i], S[j]), (sub, S[L[j, j]])) = \
    eq_piece.of(Less >> Equal[Indexed, Expr / Expr])

    S[A[i, j]], (S[L[i, :j]], S[L[j, :j]]) = sub.of(Expr - Expr @ Conjugate)

    (S[Equal(A[i, i], Norm(L[i,:i + 1]) ** 2)], S[Element(L[i, i], Interval.open(0, oo))], S[All[j:i](Equal(A[i, j], L[i, :j + 1] @ ~L[j, :j + 1]) & Element(L[i, j], S.Complexes))]), (S[i], S[0], t) = \
    All_And.of(All[And])

    return A[t, t] > Norm(L[t, :t]) ** 2, All[j:t](Equal(A[t, j], L[t, :j + 1] @ ~L[j, :j + 1]) & Element(L[t, j], S.Complexes))

@prove
def prove(Eq):
    from Axiom import Algebra, Discrete, Logic

    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    t = Symbol(domain=Range(3, n))
    Eq << apply(Equal(~A.T, A),
        Imply(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0),
        Imply(j < i, Equal(L[i, j], (A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j])),
        All[i:t](And(
            Element(L[i, i], Interval.open(0, oo)),
            Equal(A[i, i], Norm(L[i,:i + 1]) ** 2),
            All[j:i](And(
                Element(L[i, j], S.Complexes),
                Equal(A[i, j], L[i,:j + 1] @ ~ L[j,:j + 1]))))))

    Eq << Algebra.And.All.of.All_And.apply(Eq[3])

    Eq.Aii_def, Eq.Lii_is_positive = Algebra.And.All.of.All_And.apply(Eq[-2])

    Eq.Aij_def, Eq.Lij_is_complex = Algebra.And.All.of.All_And.apply(Eq[-1])

    Eq << Algebra.All.And.of.All.All.apply(Eq.Lii_is_positive, Eq.Lij_is_complex)

    Eq << Eq[2].subs(i, t).subs(j, i)

    Eq << Logic.All.of.Imp.single_variable.apply(Eq[-1], i)

    Eq << Algebra.All.And.of.All.All.apply(Eq[-1], Eq[-3])

    Eq << Discrete.All.And.of.All_And.Cholesky.apply(Eq[-1])

    Eq << Eq[1].subs(x, BlockMatrix(x[:t], 1, ZeroMatrix(n - t - 1)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ne.given.Any.Ne)

    Eq << Eq[-1].this.lhs.apply(Algebra.Any.given.Cond.subs, i, t)

    Eq << Eq[-1].this.lhs.args[:2].apply(Discrete.Dot.eq.Lamda)

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.eq.Add)

    Eq << Eq[-1].this.find(Sum[2]).limits_subs(j, i)

    Eq << Eq[-1].this.find(Sum + Sum).args[1:3].apply(Algebra.Add.eq.Sum)

    Eq << Eq[-1].subs(Eq[0][i, t].reversed)

    Eq << Eq[-1].this.find(Sum[~Mul]).apply(Algebra.Mul.eq.Sum)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.eq.Add.split.limits)

    Eq << Eq[-1].this.lhs.args[1:3].apply(Algebra.Add.eq.Sum)

    # converting A[j, i] to ~A[i, j] if j < i
    Eq << Eq[-1].subs(Eq[0][j, i].reversed)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.limits.swap.intlimit)

    # converting all A expression to L expression: A[i, j] = L[i, j] + .... if i < j
    Eq << Algebra.All.of.All_And.apply(Eq[5]).limits_subs(j, i)

    Eq << Algebra.All.of.All_Eq.Cond.subs.apply(Eq[-1], Eq[-2])

    Eq << Algebra.All.of.All_Eq.Cond.subs.apply(Eq.Aii_def, Eq[-1])

    Eq << Eq.Aij_def.this.apply(Algebra.All.limits.swap.intlimit)

    Eq << Algebra.All.of.All_Eq.Cond.subs.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.find(Indexed * Norm ** 2 * Conjugate).args[::2].apply(Algebra.Mul.Conj.eq.Square.Abs)

    Eq << Eq[-1].this.lhs.find(Add).args[:2].apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.lhs.find(Sum[~Add, Tuple, Tuple]).apply(Algebra.Add.eq.Mul.Re)

    Eq << Eq[-1].this.lhs.find(Sum[Re]).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Sum[Re]).apply(Algebra.Sum.eq.Re)

    Eq << Eq[-1].this.lhs.find(Conjugate * ~Sum).apply(Discrete.Sum.eq.Dot, simplify=1)

    Eq << Eq[-1].this.lhs.find(Sum[Re]).limits_subs(j, i, simplify=None)

    Eq << Eq[-1].this.lhs.find(Re).apply(Algebra.Re.Conj)

    Eq << Eq[-1].this.lhs.args[1:].apply(Algebra.Add.eq.Sum)

    Eq << Eq[-1].this.find(Sum).expr.args[1:].apply(Algebra.Add.eq.Re)

    Eq << Eq[-1].this.find(Re[~Add]).apply(Algebra.Add.eq.Mul)

    Eq << Eq[-1].this.find(Re, Add).apply(Discrete.Add.eq.Dot)

    Eq << Eq[-1].this.find(Re, Add).apply(Discrete.Add.eq.Dot.Block)

    Eq << Eq[-1].this.find(BlockMatrix[Conjugate]).apply(Algebra.Block.eq.Conj)

    Eq << Discrete.Gt_0.of.All_IsPositive.Gt_0.Cholesky.apply(Eq.Lii_is_positive, Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-06-22
# updated on 2023-09-18
