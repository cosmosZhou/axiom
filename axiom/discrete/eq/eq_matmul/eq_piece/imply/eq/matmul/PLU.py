from util import *


@apply
def apply(eq_initial, eq_B_def, eq_A_def):
    A, X = eq_initial.of(Equal[Indexed[0]])
    (B, k), ((S[k], S[k + ReducedArgMax(Sign(Abs(A[k, k:, k])))]), A[k]) = eq_B_def.of(Equal[Indexed, SwapMatrix @ Expr])

    n = A.shape[-1]
    block = BlockMatrix([
        [             Identity(k), ZeroMatrix(k), ZeroMatrix(k, n - k - 1)],
        [           ZeroMatrix(k),         S.One,    ZeroMatrix(n - k - 1)],
        [ZeroMatrix(n - k - 1, k), Piecewise(
            (ZeroMatrix(n - k - 1), Equal(B[k, k, k], 0)),
            (-B[k, k + 1:, k] / B[k, k, k], True)),    Identity(n - k - 1)]])

    (S[block], B[k]), A[k + 1] = eq_A_def.of(Equal[MatMul])
    return Equal(X, MatProduct[k:n](SwapMatrix(n, k, k + ReducedArgMax(Sign(Abs(A[k, k:, k])))).T @ MatProduct[k:n](block) @ B[n - 1]))

@prove(proved=False)
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    n = 7
    X = Symbol(shape=(n, n), complex=True)
    A, B = Symbol(shape=(n, n, n), complex=True)
    k = Symbol(integer=True)
    Eq << apply(
        Equal(A[0], X),
        Equal(B[k], SwapMatrix(n, k, k + ReducedArgMax(Sign(Abs(A[k, k:, k])))) @ A[k]),
        Equal(A[k + 1], BlockMatrix([
            [Identity(k), ZeroMatrix(k), ZeroMatrix(k, n - k - 1)],
            [ZeroMatrix(k), S.One, ZeroMatrix(n - k - 1)],
            [ZeroMatrix(n - k - 1, k), Piecewise(
                (ZeroMatrix(n - k - 1), Equal(B[k, k, k], 0)),
                (-B[k, k + 1:, k] / B[k, k, k], True)), Identity(n - k - 1)]
        ]) @ B[k]))

    i, j = Symbol(integer=True)
    Eq << Equal(X, Lamda[j:n, i:n](i ** j), plausible=None)

    Eq << Eq[-1].this.find(Lamda).doit()

    Eq << algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq[-1])

    Eq << Eq[1].subs(k, 0)

    Eq.back_subs0 = discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1], left=True)

    Eq.back_subs0 = algebra.eq.eq.imply.eq.transit.apply(Eq[0], Eq.back_subs0)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[2].subs(k, 0)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[1].subs(k, 1)

    Eq.back_subs1 = discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1], left=True)

    Eq.back_subs1 = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq.back_subs1)

    Eq.back_subs1 = discrete.eq_matmul.imply.eq.inverse.apply(Eq.back_subs1, left=True)

    Eq.back_subs1 = Eq.back_subs1.this.find(MatPow).apply(discrete.inverse.to.block)

    Eq.back_subs1 = Eq.back_subs1.this.find(-Piecewise).apply(algebra.mul.piece.to.piece)

    Eq.back_subs1 = Eq.back_subs0.subs(Eq.back_subs1)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[2].subs(k, 1)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[1].subs(k, 2)

    Eq.back_subs2 = discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1], left=True)

    Eq.back_subs2 = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq.back_subs2)

    Eq.back_subs2 = discrete.eq_matmul.imply.eq.inverse.apply(Eq.back_subs2, left=True)

    Eq.back_subs2 = Eq.back_subs2.this.find(MatPow).apply(discrete.inverse.to.block)

    Eq.back_subs2 = Eq.back_subs2.this.find(-Piecewise).apply(algebra.mul.piece.to.piece)

    Eq.back_subs2 = Eq.back_subs1.subs(Eq.back_subs2)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[2].subs(k, 2)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[1].subs(k, 3)

    Eq.back_subs3 = discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1], left=True)

    Eq.back_subs3 = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq.back_subs3)

    Eq.back_subs3 = discrete.eq_matmul.imply.eq.inverse.apply(Eq.back_subs3, left=True)

    Eq.back_subs3 = Eq.back_subs3.this.find(MatPow).apply(discrete.inverse.to.block)

    Eq.back_subs3 = Eq.back_subs3.this.find(-Piecewise).apply(algebra.mul.piece.to.piece)

    Eq.back_subs3 = Eq.back_subs2.subs(Eq.back_subs3)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[2].subs(k, 3)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[1].subs(k, 4)

    Eq.back_subs4 = discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1], left=True)

    Eq.back_subs4 = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq.back_subs4)

    Eq.back_subs4 = discrete.eq_matmul.imply.eq.inverse.apply(Eq.back_subs4, left=True)

    Eq.back_subs4 = Eq.back_subs4.this.find(MatPow).apply(discrete.inverse.to.block)

    Eq.back_subs4 = Eq.back_subs4.this.find(-Piecewise).apply(algebra.mul.piece.to.piece)

    Eq.back_subs4 = Eq.back_subs3.subs(Eq.back_subs4)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[2].subs(k, 4)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[1].subs(k, 5)

    Eq.back_subs5 = discrete.eq_matmul.imply.eq.inverse.apply(Eq[-1], left=True)

    Eq.back_subs5 = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq.back_subs5)

    Eq.back_subs5 = discrete.eq_matmul.imply.eq.inverse.apply(Eq.back_subs5, left=True)

    Eq.back_subs5 = Eq.back_subs5.this.find(MatPow).apply(discrete.inverse.to.block)

    Eq.back_subs5 = Eq.back_subs5.this.find(-Piecewise).apply(algebra.mul.piece.to.piece)

    Eq.back_subs5 = Eq.back_subs4.subs(Eq.back_subs5)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[2].subs(k, 5)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(discrete.matmul.to.matrix)

    Eq << Eq[1].subs(k, 6)

    Eq.back_subs6 = Eq[-1].reversed

    Eq.back_subs6 = algebra.eq.eq.imply.eq.transit.apply(Eq[-4], Eq.back_subs6)

    Eq.back_subs6 = discrete.eq_matmul.imply.eq.inverse.apply(Eq.back_subs6, left=True)

    Eq.back_subs6 = Eq.back_subs6.this.find(MatPow).apply(discrete.inverse.to.block)

    Eq.back_subs6 = Eq.back_subs6.this.find(-Piecewise).apply(algebra.mul.piece.to.piece)

    Eq.back_subs6 = Eq.back_subs5.subs(Eq.back_subs6)

    Eq.back_subs6 = Eq.back_subs6.subs(Eq[6], Eq[8], Eq[11], Eq[13], Eq[16], Eq[18], Eq[21], Eq[23], Eq[26], Eq[28], Eq[31], Eq[33], Eq[37], Eq[36])

    Eq.back_subs6 = Eq.back_subs6.this.find(BlockMatrix).apply(algebra.expr.to.matrix).this.find(BlockMatrix).apply(algebra.expr.to.matrix).this.find(BlockMatrix).apply(algebra.expr.to.matrix).this.find(BlockMatrix).apply(algebra.expr.to.matrix).this.find(BlockMatrix).apply(algebra.expr.to.matrix).this.find(BlockMatrix).apply(algebra.expr.to.matrix)

    Eq.back_subs6 = Eq.back_subs6.this.rhs.args[0:2].apply(discrete.matmul.to.matrix).this.rhs.args[0:2].apply(discrete.matmul.to.matrix).this.rhs.args[0:2].apply(discrete.matmul.to.matrix).this.rhs.args[0:2].apply(discrete.matmul.to.matrix).this.rhs.args[0:2].apply(discrete.matmul.to.matrix)

    B = Eq.back_subs6.rhs.args[1].T
    Eq << (B / Lamda[i:n](Factorial(i))).this.find(Lamda).apply(algebra.lamda.to.matrix)

    Eq << Eq[-1].this.rhs.apply(algebra.expr.to.matrix)

    Eq << Lamda[j:n, i:n](Stirling(i, j)).this.apply(algebra.expr.to.matrix)

    Eq << Lamda[j:n, i:n](Binomial(i, j)).this.apply(algebra.expr.to.matrix)

    
    


if __name__ == '__main__':
    run()
# created on 2023-08-19
# updated on 2023-10-03
