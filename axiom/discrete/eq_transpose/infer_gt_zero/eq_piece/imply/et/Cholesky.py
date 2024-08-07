from util import *


@apply
def apply(eq, infer, eq_piece):
    from axiom.discrete.eq_transpose.infer_gt_zero.eq_piece.imply.all.et.Cholesky import extract
    A, L, x, i, j = extract(eq, infer, eq_piece)
    return Element(L, CartesianSpace(Reals, *A.shape)), Equal(A, L @ L.T)

@prove
def prove(Eq):
    from axiom import discrete, algebra, sets

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

    t = Symbol(positive=True, integer=True)
    Eq << discrete.eq_transpose.infer_gt_zero.eq_piece.imply.all.et.Cholesky.apply(*Eq[:3], t)

    Eq << Eq[-1].subs(t, n)

    Eq << Eq[-1].simplify()

    Eq.A_diagonal, *Eq[-2:] = algebra.et.imply.et.apply(Eq[-1], None)

    Eq <<= algebra.all_et.imply.et.all.apply(Eq[-1]), sets.el.imply.el.relax.apply(Eq[-2], Reals)

    Eq.A_lower = algebra.all.imply.infer.apply(Eq[-3])

    Eq.L_lower = algebra.cond.all.imply.all.push.apply(Eq[-1], Eq[-2])

    Eq << algebra.all.imply.all.limits.domain_defined.apply(Eq[-3])

    Eq.L_is_zero = algebra.cond_piece.imply.infer.apply(Eq[2], -1)

    Eq << Eq.L_is_zero.this.rhs.apply(sets.eq.imply.el.finiteset)

    Eq << Eq[-1].this.rhs.apply(sets.el.imply.el.relax, Reals)

    Eq << algebra.infer.imply.all.apply(Eq[-1], j)

    Eq << algebra.all.all.imply.all.limits_union.apply(Eq[-1], Eq.L_lower)

    Eq << Eq[-1].this(i).find(Union).simplify()

    Eq << sets.el.imply.el.cartesianSpace.apply(Eq[-1], (j, 0, n), (i, 0, n), simplify=None)

    Eq << Eq[4].rhs.this.apply(discrete.matmul.to.lamda, var=i)

    Eq << Eq[-1].this.find(Sum).apply(discrete.sum.to.matmul, simplify=1)

    Eq << Eq[0][i, j]

    k = Symbol(integer=True)
    Eq << Eq.A_lower.subs(i, k).subs(j, i).subs(k, j)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << algebra.infer.imply.all.apply(Eq[-1])

    Eq << algebra.all.imply.all.limits.domain_defined.apply(Eq[-1])

    Eq.A_ij = Equal(A[i, j], Piecewise(
        (Eq.A_lower.rhs.rhs, j < i),
        (Eq[-1].expr.rhs, j > i),
        (Eq.A_diagonal.rhs, True)), plausible=True)

    Eq.lt_infer, Eq.gt_infer, Eq.eq_infer = algebra.cond_piece.given.et.infer.apply(Eq.A_ij)

    Eq << algebra.infer.given.all.apply(Eq.lt_infer)

    Eq << algebra.infer.given.all.apply(Eq.gt_infer, i)

    Eq << algebra.infer.given.infer.subs.apply(Eq.eq_infer)

    Eq << algebra.infer.given.cond.apply(Eq[-1])

    Eq <<= algebra.all.given.all.limits.domain_defined.apply(Eq[-3]), algebra.all.given.all.limits.domain_defined.apply(Eq[-2])

    Eq << Eq.A_ij.this.rhs.apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.rhs.apply(algebra.piece.et.invert, 0)

    Eq << Infer(Equal(j, i), Equal(Eq[-1].rhs.args[1].expr, Eq[-1].rhs.args[2].expr), plausible=True)

    Eq << algebra.infer.given.infer.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.lhs.apply(discrete.square.norm.to.matmul.conj, swap=True)

    Eq << algebra.infer.imply.eq.piece.apply(Eq[-2], Eq[-3].rhs)

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].expr.T

    Eq << algebra.cond_piece.imply.infer.apply(Eq[-1], 1)

    Eq <<= algebra.infer.imply.infer.et.apply(Eq.lt_infer), algebra.infer.imply.infer.et.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Less).apply(algebra.lt.imply.eq.min, reverse=True), Eq[-1].this.rhs.find(GreaterEqual).apply(algebra.ge.imply.eq.min, reverse=True)

    Eq <<= Eq[-2].this.rhs.args[0] + 1, Eq[-1].this.rhs.args[0] + 1

    Eq <<= Eq[-2].this.rhs.apply(algebra.eq.eq.imply.eq.subs, swap=True), Eq[-1].this.rhs.apply(algebra.eq.eq.imply.eq.subs, swap=True)


    Eq <<= Eq[-1] & Eq[-2]
    Eq << discrete.imply_is_zero.imply.eq.matmul.apply(Eq.L_is_zero)
    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[-2], Eq[-1])
    Eq << algebra.eq.imply.eq.lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))




if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-06-29
