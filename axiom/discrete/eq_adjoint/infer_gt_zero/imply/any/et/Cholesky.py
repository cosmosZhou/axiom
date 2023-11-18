from util import *


@apply
def apply(eq, infer, L, i, j):
    A, S[A] = eq.of(Equal[Adjoint])
    x, S[(~x) @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    assert L.is_complex
    return Exists[L](Equal(A, L @ ~L.T) & Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ ~L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    L = Symbol(shape=(n, n), complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(~A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), ~x @ A @ x > 0), L, i, j)

    L_quote = Symbol(super_complex=True, shape=(n, n))
    Eq << Exists[L_quote](Eq[2].find(Equal[Indexed])._subs(L, L_quote), plausible=True)

    Eq << algebra.any_piece.given.et.infer.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.simplify()

    Eq <<= algebra.infer.given.all.apply(Eq[-3]), algebra.infer.given.infer.subs.apply(Eq[-2])

    Eq <<= algebra.all.given.all.limits.domain_defined.apply(Eq[-2]), Eq[-1].this.rhs.simplify()

    Eq <<= Eq[-2].this(i).find(Min).simplify(), algebra.infer.given.cond.apply(Eq[-1])

    Eq <<= Eq[-2].this(j).expr.args[1].args[0].apply(algebra.expr.to.block, i + 1), Eq[-1].this(i).apply(algebra.any.limits.pop.slice)

    Eq <<= Eq[-2].this(j).expr.simplify(), Eq[-1].this.apply(algebra.any.limits.swap)

    Eq << Eq[-1].this.apply(algebra.any.limits.separate)

    Eq << Eq[-2].this(i).expr.apply(algebra.any.limits.pop.slice)

    Eq << Eq[-1].this.expr.apply(algebra.any.limits.swap)

    Eq << Eq[-1].this(j).expr.apply(algebra.any.limits.separate)

    Eq << Eq[-1].this(j).expr.apply(algebra.any.limits.pop.slice)

    Eq << Eq[-1].this.expr.apply(algebra.any.limits.swap)

    Eq << Eq[-1].this(j).expr.apply(algebra.any.limits.separate)

    Eq << algebra.cond.any.imply.any.et.apply(Eq[0] & Eq[1], Eq[3], simplify=None)

    Eq << Eq[-1].this.expr.apply(discrete.eq_adjoint.infer_gt_zero.eq_piece.imply.et.Cholesky, simplify=False, ret=0)

    Eq << algebra.any.given.any.subs.apply(Eq[2], L, L_quote)





if __name__ == '__main__':
    run()
# created on 2023-07-01
# updated on 2023-07-02
