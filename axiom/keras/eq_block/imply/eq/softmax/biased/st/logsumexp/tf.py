from util import *


@apply
def apply(eq):
    (H, (((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], S[n + 1 - Min(n, u)])), (S[A[i + n + 1 - Min(n, u), i + n - Min(n, u) + 1:]], (S[i], S[0], S[Min(n, u) - 1])))), ((S[H[i]], S[A[i, relu(i - l + 1):Min(n, i + u)]]), (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[1][ZeroMatrix, Expr, ZeroMatrix] + BlockMatrix[1][
            BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Sliced[Indexed]
                    ],
                    Tuple[Min - 1]
                ],
                Lamda
            ],
            BlockMatrix[
                Lamda[Sliced[Tuple[Add[Min]]]],
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix
                    ]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp[Add[BlockMatrix[ZeroMatrix, Expr, ZeroMatrix]]]]])
    assert n >= 2 and u >= 2 and l >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + H * Identity(n) + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo),
                 BlockMatrix(
                    Lamda[i:Min(l, n) - 1](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), ZeroMatrix(n - i))),
                    Lamda[i:n - Min(l, n) + 1](BlockMatrix(ZeroMatrix(i), Exp(z[i + Min(l, n) - 1, :Min(l, n) - 1]), ZeroMatrix(n - i - Min(l, n) + 1)))
                 ) + BlockMatrix(
                    Lamda[i:n - Min(u, n) + 1](BlockMatrix(ZeroMatrix(i), Exp(z[i, Min(l, n) - 1:]), ZeroMatrix(n - i - Min(u, n)))),
                    Lamda[i:Min(u, n) - 1](BlockMatrix(ZeroMatrix(n - Min(u, n) + i + 1), Exp(z[i + n - Min(u, n) + 1, Min(l, n) - 1:breadth - i - 1])))
                 ))


@prove
def prove(Eq):
    from axiom import algebra, keras

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](ZeroMatrix(n, Min(l, n) - 1), H, ZeroMatrix(n, Min(u, n) - 1)) + BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n) - 1](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i, :i])),
            Lamda[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])
        ),
        BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1)))
        )) - Lamda[i:n](OneMatrix(breadth) * logsumexp((A[i, relu(i + 1 - l):Min(n, i + u)] + BlockMatrix(ZeroMatrix(Min(i, l - 1)), H[i], ZeroMatrix(Min(n - i, u) - 1)))))))

    Eq << BlockMatrix[1](H, ZeroMatrix(n, Min(u, n) - 1)).this.apply(algebra.block.split, n + 1 - Min(u, n))

    Eq << Eq[0].find(BlockMatrix[1][ZeroMatrix]).this.subs(Eq[-1])

    Eq << Eq[0].subs(Eq[-1])

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(algebra.add.block.to.block)

    Eq << Eq[-1].this.rhs.find(Add[BlockMatrix]).apply(algebra.add.block.to.block)

    Eq.z_def = Eq[-3].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i]

    Eq.left_upper_part = Eq[-1].this.find(Lamda)().expr.simplify()

    Eq << Eq.A_def[i + Min(l, n) - 1][i:i + Min(l, n) - 1]

    Eq.left_lower_part = Eq[-1].this.find(Lamda)().expr.simplify()

    Eq << Eq.A_def[i + n + 1 - Min(u, n)][i + n + 1 - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.delta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.delta.to.block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(algebra.mul.to.block)

    Eq.matmul_subs = Eq[-1].this.apply(algebra.eq.transport, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(Add[2]).this.args[0].apply(algebra.expr.to.lamda, i)

    Eq << Eq[-1].this.rhs.apply(algebra.add.to.lamda)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.expr.to.lamda)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(algebra.mul.to.piece)

    Eq << Eq[-1].this.rhs.find(Add).apply(algebra.add.piece.to.piece)

    Eq << Eq[-1].this.find(Piecewise).apply(algebra.piece.swap, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(algebra.add.to.piece)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(algebra.piece.unnest)

    Eq.lower_part = Eq[-1].this.rhs.apply(algebra.lamda.piece.to.lamda.block)

    Eq << Eq.A_def[i]#[i:i + Min(u, n)]

    Eq << algebra.cond.imply.all.restrict.apply(Eq[-1], (i, 0, n + 1 - Min(u, n)))

    Eq << algebra.all_eq.imply.all.eq.slice.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.delta.offset, -i)

    Eq << Eq[-1].this.find(Mul).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.delta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.delta.to.block)

    Eq << Eq[-1].this.find(Mul).apply(algebra.mul.to.block)

    Eq << algebra.all_eq.imply.eq.lamda.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(algebra.lamda.to.add)

    Eq.upper_part = Eq[-1].this.find(Lamda[BlockMatrix]).apply(algebra.lamda.block.to.block.lamda)

    Eq << Eq.A_def[i][relu(i + 1 - l):Min(n, i + u)]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(algebra.delta.offset, -i)

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(algebra.expr.to.lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.delta.to.mul.lamda)

    Eq << Eq[-1].this.find(Lamda).apply(algebra.lamda.delta.to.block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(algebra.mul.to.block)

    Eq << Eq[-1].this.find(ZeroMatrix).shape[0].find(relu).apply(keras.relu.to.add.min)

    Eq << Eq[-1].this.find(ZeroMatrix).shape[0].apply(algebra.add.to.min)

    Eq << Eq[-1].this.find(BlockMatrix).args[2].shape[0].find(Min).apply(algebra.min.to.add, i)

    Eq << Eq.z_def.subs(Eq.left_upper_part.reversed, Eq.left_lower_part.reversed, Eq[-1].reversed, Eq.upper_part.reversed, Eq.lower_part)
    Eq << keras.eq_block.imply.eq.softmax.st.logsumexp.tf.apply(Eq[-1])
    Eq << Eq[-1].this.find(Symbol).definition




if __name__ == '__main__':
    run()
# created on 2022-03-15
# updated on 2023-09-17
