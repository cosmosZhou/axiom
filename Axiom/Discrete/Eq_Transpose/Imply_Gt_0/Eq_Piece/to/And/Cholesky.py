from util import *


@apply
def apply(eq, infer, eq_piece):
    from Axiom.Discrete.Eq_Transpose.Imply_Gt_0.Eq_Piece.to.All.And.Cholesky import extract
    A, L, x, i, j = extract(eq, infer, eq_piece)
    return Element(L, CartesianSpace(Reals, *A.shape)), Equal(A, L @ L.T)

@prove
def prove(Eq):
    from Axiom import Discrete, Algebra, Sets

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A.T, A),
               Imply(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j], j < i), (sqrt(A[i, i] - Norm(L[i, :i]) ** 2), Equal(j, i)), (0, True))))

    t = Symbol(positive=True, integer=True)
    Eq << Discrete.Eq_Transpose.Imply_Gt_0.Eq_Piece.to.All.And.Cholesky.apply(*Eq[:3], t)

    Eq << Eq[-1].subs(t, n)

    Eq << Eq[-1].simplify()

    Eq.A_diagonal, *Eq[-2:] = Algebra.And.to.And.apply(Eq[-1], None)

    Eq <<= Algebra.All_And.to.And.All.apply(Eq[-1]), Sets.In.to.In.relax.apply(Eq[-2], Reals)

    Eq.A_lower = Algebra.All.to.Imply.apply(Eq[-3])

    Eq.L_lower = Algebra.Cond.All.to.All.push.apply(Eq[-1], Eq[-2])

    Eq << Algebra.All.to.All.limits.domain_defined.apply(Eq[-3])

    Eq.L_is_zero = Algebra.Cond_Piece.to.Imply.apply(Eq[2], -1)

    Eq << Eq.L_is_zero.this.rhs.apply(Sets.Eq.to.In.FiniteSet)

    Eq << Eq[-1].this.rhs.apply(Sets.In.to.In.relax, Reals)

    Eq << Algebra.Imply.to.All.apply(Eq[-1], j)

    Eq << Algebra.All.All.to.All.limits_union.apply(Eq[-1], Eq.L_lower)

    Eq << Eq[-1].this(i).find(Union).simplify()

    Eq << Sets.In.to.In.CartesianSpace.apply(Eq[-1], (j, 0, n), (i, 0, n), simplify=None)

    Eq << Eq[4].rhs.this.apply(Discrete.Dot.eq.Lamda, var=i)

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.eq.Dot, simplify=1)

    Eq << Eq[0][i, j]

    k = Symbol(integer=True)
    Eq << Eq.A_lower.subs(i, k).subs(j, i).subs(k, j)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Algebra.Imply.to.All.apply(Eq[-1])

    Eq << Algebra.All.to.All.limits.domain_defined.apply(Eq[-1])

    Eq.A_ij = Equal(A[i, j], Piecewise(
        (Eq.A_lower.rhs.rhs, j < i),
        (Eq[-1].expr.rhs, j > i),
        (Eq.A_diagonal.rhs, True)), plausible=True)

    Eq.lt_infer, Eq.gt_infer, Eq.eq_infer = Algebra.Cond_Piece.of.And.Imply.apply(Eq.A_ij)

    Eq << Algebra.Imply.of.All.apply(Eq.lt_infer)

    Eq << Algebra.Imply.of.All.apply(Eq.gt_infer, i)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq.eq_infer)

    Eq << Algebra.Imply.of.Cond.apply(Eq[-1])

    Eq <<= Algebra.All.of.All.limits.domain_defined.apply(Eq[-3]), Algebra.All.of.All.limits.domain_defined.apply(Eq[-2])

    Eq << Eq.A_ij.this.rhs.apply(Algebra.Piece.swap, 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.And.invert, 0)

    Eq << Imply(Equal(j, i), Equal(Eq[-1].rhs.args[1].expr, Eq[-1].rhs.args[2].expr), plausible=True)

    Eq << Algebra.Imply.of.Imply.subs.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.lhs.apply(Discrete.Square.Norm.eq.Dot.Conj, swap=True)

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq[-2], Eq[-3].rhs)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-4], Eq[-1])

    Eq << Eq[-1].this.rhs.args[1].expr.T

    Eq << Algebra.Cond_Piece.to.Imply.apply(Eq[-1], 1)

    Eq <<= Algebra.Imply.to.Imply.And.apply(Eq.lt_infer), Algebra.Imply.to.Imply.And.apply(Eq[-1])

    Eq <<= Eq[-2].this.rhs.find(Less).apply(Algebra.Lt.to.Eq.Min, reverse=True), Eq[-1].this.rhs.find(GreaterEqual).apply(Algebra.Ge.to.Eq.Min, reverse=True)

    Eq <<= Eq[-2].this.rhs.args[0] + 1, Eq[-1].this.rhs.args[0] + 1

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs, swap=True), Eq[-1].this.rhs.apply(Algebra.Eq.Eq.to.Eq.subs, swap=True)


    Eq <<= Eq[-1] & Eq[-2]
    Eq << Discrete.Imply_Eq_0.to.Eq.Dot.apply(Eq.L_is_zero)
    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[-2], Eq[-1])
    Eq << Algebra.Eq.to.Eq.Lamda.apply(Eq[-1], (j, 0, n), (i, 0, n))




if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-06-29
