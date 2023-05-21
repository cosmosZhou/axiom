from util import *


@apply
def apply(eq, infer, eq_piece):
    A, S[A] = eq.of(Equal[Transpose])
    x, S[(~x) @ A @ x] = infer.of(Infer[Unequal[0], Expr > 0])
    (L, i, j), ecs = eq_piece.of(Equal[Indexed, Piecewise])
    return L[i, i] > 0

@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    n = Symbol(domain=Range(10, oo))
    A = Symbol(shape=(n, n), real=True)
    x = Symbol(shape=(n,), real=True)
    L = Symbol(shape=(n, n), super_real=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A.T, A),
               Infer(Unequal(x, ZeroMatrix(n)), x @ A @ x > 0),
               Equal(L[i, j], Piecewise(((A[i, j] - L[i, :j] @ L[j, :j]) / L[j, j], i > j), (sqrt(A[i, j] - L[i, :j] @ L[j, :j]), Equal(i, j)), (0, True))))

    Eq << algebra.all_gt_zero.imply.gt_zero.positive_definite.apply(Eq[1], i)

    Eq << Eq[-1].subs(i, 0)

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1])

    Eq << Eq[2].subs(i, 0).subs(j, 0)

    Eq << algebra.eq.gt.imply.gt.transit.apply(Eq[-1], Eq[-2])

    Eq << Eq[2].subs(i, 1).subs(j, 1)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[2].subs(i, 1).subs(j, 0)

    Eq << Eq[-2].subs(Eq[-1])

    t = Symbol(real=True, shape=(oo,))
    Eq << Eq[1].subs(x, Lamda[i:n](Piecewise((t[0], Equal(i, 0)), (1, Equal(i, 1)), (0, True))))

    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.any.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.cond.subs, i, 1)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq[0][0, 1]

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-2].subs(t[0], -(A[1, 0] / L[0, 0] ** 2))

    Eq << Eq[-1].subs(Eq[7].reversed ** 2)

    Eq << algebra.gt_zero.imply.gt_zero.sqrt.apply(Eq[-1])

    Eq << algebra.eq.gt.imply.gt.transit.apply(Eq[12], Eq[-1])

    Eq << Eq[2].subs(i, 2).subs(j, 2)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[-1].this.find(Sum).apply(algebra.sum.to.add.doit)

    Eq << Eq[2].subs(i, 2).subs(j, 1)

    Eq << Eq[-1].this.find(MatMul).apply(discrete.matmul.to.sum)

    Eq << Eq[2].subs(i, 2).subs(j, 0)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].subs(Eq[11])

    Eq << Eq[27].subs(Eq[30], Eq[-1])

    Eq << Eq[-1].this.find(Add ** 2).apply(algebra.pow.to.add)

    Eq << Eq[1].subs(x, Lamda[i:n](Piecewise((t[0], Equal(i, 0)), (t[1], Equal(i, 1)), (1, Equal(i, 2)), (0, True))))

    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.any.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.cond.subs, i, 2)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << Eq[0][0, 2]

    Eq << Eq[0][1, 2]

    Eq << Eq[-3].subs(Eq[-1].reversed, Eq[-2].reversed, Eq[18].reversed)

    Eq << Eq[-1].subs(Eq[7].reversed ** 2)

    Eq << Eq[12].reversed ** 2

    Eq << Eq[-1] - Eq[-1].lhs.args[1]

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    
    return
    Eq << Eq[-1].this.lhs.apply(algebra.poly.square_completing, t[1])

    Eq << Eq[-1].subs(t[1], -Eq[-1].find((~Add) ** 2).args[1])

    Eq << Eq[-1].this.lhs.apply(algebra.poly.square_completing, t[0])

    Eq << Eq[-1].find((~Add) ** 2).args[1]

    Eq << Eq[-1].subs(t[0], -Eq[-1].find((~Add) ** 2).args[1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(algebra.mul.to.add)

    


if __name__ == '__main__':
    run()
# created on 2023-05-01
# updated on 2023-05-06
