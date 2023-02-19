from util import *


@apply
def apply(eq):
    (H, ((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], S[n - Min(n, u) + 1])), (S[A[i + n - Min(u, n) + 1, i + n - Min(n, u) + 1:]], (S[i], S[0], S[Min(u, n) - 1]))), ((S[H[i]], S[A[i, i:Min(n, i + u)]]), (S[i], S[0], S[n]))), z = \
    eq.of(
        Equal[
            BlockMatrix[1][Expr, ZeroMatrix] + BlockMatrix[
                Lamda[Sliced[Indexed, Tuple[Add[Min]]]],
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix
                    ],
                ]
            ] - Lamda[OneMatrix * logsumexp[Add[BlockMatrix[Expr, ZeroMatrix]]]]])
    assert n >= 2 and u >= 2
    breadth = Min(u, n) - 1
    return Equal(softmax(A + H * Identity(n) + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                     Lamda[i:n - breadth](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - 1 - i - breadth))),
                     Lamda[i:breadth](BlockMatrix(ZeroMatrix(n - breadth + i), Exp(z[i + n - breadth, :breadth - i])))))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    z = Symbol(shape=(n, Min(u, n)), real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](H, ZeroMatrix(n, Min(u, n) - 1)) + BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1)))) - Lamda[i:n](OneMatrix(Min(u, n)) * logsumexp((A[i, i:Min(n, i + u)] + BlockMatrix(H[i], ZeroMatrix(Min(n - i, u) - 1)))))))

    Eq << Eq[0].this.find(BlockMatrix[1]).apply(algebra.block.split, n + 1 - Min(u, n))

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(algebra.add_block.to.block)

    Eq.z_def = Eq[-2].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i + n + 1 - Min(u, n)][i + n + 1 - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(algebra.mul.to.block)

    Eq.matmul_subs = Eq[-1].this.apply(algebra.eq.transport, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add[2]).this.args[0].apply(algebra.expr.to.lamda, i)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.expr.to.lamda)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add_piece.to.piece)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(algebra.piece.flatten)

    Eq.lower_part = Eq[-1].this.rhs.apply(algebra.lamda.piece.to.block)

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n + 1 - Min(u, n)))

    Eq << algebra.all_eq.imply.all_eq.slice.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.offset, -i)

    Eq << Eq[-1].this.find(Mul).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.block)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.block)

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    Eq.upper_part = Eq[-1].this.find(Lamda[BlockMatrix]).apply(algebra.lamda_block.to.block.lamda)

    Eq << Eq.A_def[i][i:Min(n, i + u)]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.kroneckerDelta.offset, -i)

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda_kroneckerDelta.to.block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(algebra.mul.to.block)

    Eq << Eq.z_def.subs(Eq[-1].reversed, Eq.upper_part.reversed, Eq.lower_part)

    Eq << keras.eq_block.imply.eq.softmax.upper_triangle.st.logsumexp.tf.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition




if __name__ == '__main__':
    run()
# created on 2022-03-14
