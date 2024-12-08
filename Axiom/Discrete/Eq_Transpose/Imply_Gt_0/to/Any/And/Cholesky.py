from util import *


@apply
def apply(eq, infer, L, i, j):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[x @ A @ x] = infer.of(Imply[Unequal[0], Expr > 0])
    assert L.is_real
    return Exists[L](Equal(A, L @ L.T) & Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), real=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A.T, A),
               Imply(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0), L, i, j)

    L_quote = Symbol(super_real=True, shape=(n, n))
    Eq << Exists[L_quote](Eq[2].find(Equal[Indexed])._subs(L, L_quote), plausible=True)

    Eq << Algebra.Any_Piece.of.And.Imply.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.simplify()

    Eq <<= Algebra.Imply.of.All.apply(Eq[-3]), Algebra.Imply.of.Imply.subs.apply(Eq[-2])

    Eq <<= Algebra.All.of.All.limits.domain_defined.apply(Eq[-2]), Eq[-1].this.rhs.simplify()

    Eq <<= Eq[-2].this(i).find(Min).simplify(), Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq <<= Eq[-2].this(j).expr.args[1].args[0].apply(Algebra.Expr.eq.Block, i + 1), Eq[-1].this(i).apply(Algebra.Any.limits.pop.Slice)

    Eq <<= Eq[-2].this(j).expr.simplify(), Eq[-1].this.apply(Algebra.Any.limits.swap)

    Eq << Eq[-1].this.apply(Algebra.Any.limits.separate)

    Eq << Eq[-2].this(i).expr.apply(Algebra.Any.limits.pop.Slice)

    Eq << Eq[-1].this.expr.apply(Algebra.Any.limits.swap)

    Eq << Eq[-1].this(j).expr.apply(Algebra.Any.limits.separate)
    Eq << Eq[-1].this(j).expr.apply(Algebra.Any.limits.pop.Slice)
    Eq << Eq[-1].this.expr.apply(Algebra.Any.limits.swap)
    Eq << Eq[-1].this(j).expr.apply(Algebra.Any.limits.separate)

    Eq << Algebra.Cond.Any.to.Any.And.apply(Eq[0] & Eq[1], Eq[3], simplify=None)

    Eq << Eq[-1].this.expr.apply(Discrete.Eq_Transpose.Imply_Gt_0.Eq_Piece.to.And.Cholesky, simplify=False, ret=0)

    Eq << Algebra.Any.of.Any.subs.apply(Eq[2], L, L_quote)




if __name__ == '__main__':
    run()
# created on 2023-07-02
