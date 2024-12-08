from util import *


@apply
def apply(eq):
    (H, (((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], S[n - Min(n, u)])), (S[A[i + n - Min(n, u), i + n - Min(n, u):]], (S[i], S[0], S[Min(n, u)])))), ((S[H[i]], S[A[i, relu(i - l + 1):Min(n, i + u)]]), (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[1][ZeroMatrix, Expr, ZeroMatrix] + BlockMatrix[1][
            BlockMatrix[
                Lamda[
                    BlockMatrix[
                        NegativeInfinity * OneMatrix,
                        Sliced[Indexed]
                    ],
                    Tuple[Min]
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
                    Lamda[i:Min(l, n)](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), ZeroMatrix(n - i))),
                    Lamda[i:n - Min(l, n)](BlockMatrix(ZeroMatrix(i + 1), Exp(z[i + Min(l, n), :Min(l, n) - 1]), ZeroMatrix(n - i - Min(l, n))))
                 ) + BlockMatrix(
                    Lamda[i:n - Min(u, n)](BlockMatrix(ZeroMatrix(i), Exp(z[i, Min(l, n) - 1:]), ZeroMatrix(n - i - Min(u, n)))),
                    Lamda[i:Min(u, n)](BlockMatrix(ZeroMatrix(n - Min(u, n) + i), Exp(z[i + n - Min(u, n), Min(l, n) - 1:breadth - i])))
                 ))


@prove
def prove(Eq):
    from Axiom import Algebra, Keras

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    H = Symbol(shape=(n,), real=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix[1](ZeroMatrix(n, Min(l, n) - 1), H, ZeroMatrix(n, Min(u, n) - 1)) + BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n)](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i, :i])),
            Lamda[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])
        ),
        BlockMatrix(
            Lamda[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * OneMatrix(i)))
        )) - Lamda[i:n](OneMatrix(breadth) * logsumexp((A[i, relu(i + 1 - l):Min(n, i + u)] + BlockMatrix(ZeroMatrix(i - relu(i - l + 1)), H[i], ZeroMatrix(-i + Min(n, i + u) - 1)))))))

    Eq << BlockMatrix[1](H, ZeroMatrix(n, Min(u, n) - 1)).this.apply(Algebra.Block.split, n - Min(u, n))

    Eq << Eq[0].find(BlockMatrix[1][ZeroMatrix]).this.subs(Eq[-1])

    Eq << Eq[0].subs(Eq[-1])

    Eq << Add(*Eq[-1].find(Add[BlockMatrix]).args[:2]).this.apply(Algebra.Add.Block.eq.Block)

    Eq << Eq[-1].this.rhs.find(Add[BlockMatrix]).apply(Algebra.Add.Block.eq.Block)

    Eq.z_def = Eq[-3].subs(Eq[-1])

    A = Symbol(Add(*Eq[1].lhs.arg.args[:2]))
    Eq.A_def = A.this.definition

    Eq << Eq.A_def[i][:i]

    Eq.left_upper_part = Eq[-1].this.find(Lamda)().expr.simplify()

    Eq << Eq.A_def[i + Min(l, n)][i + 1:i + Min(l, n)]

    Eq.left_lower_part = Eq[-1].this.find(Lamda)().expr.simplify()

    Eq << Eq.A_def[i + n - Min(u, n)][i + n - Min(u, n):]

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(Algebra.Expr.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Mul.Lamda)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq.matmul_subs_right = Eq[-1].this.apply(Algebra.Eq.transport, rhs=0).reversed

    Eq << Eq.z_def.rhs.find(BlockMatrix[1] + Lamda[BlockMatrix]).this.args[0].apply(Algebra.Expr.eq.Lamda, i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add.eq.Lamda)

    Eq << Eq[-1].this.rhs.subs(Eq.matmul_subs_right)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Expr.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(-Piecewise).apply(Algebra.Mul.eq.Piece)

    Eq << Eq[-1].this.rhs.find(Add).apply(Algebra.Add.Piece.eq.Piece)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap, 1)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.rhs.find(Add[Piecewise]).apply(Algebra.Add.eq.Piece)

    Eq << Eq[-1].this.rhs.find(Piecewise).apply(Algebra.Piece.unnest)

    Eq.lower_part = Eq[-1].this.rhs.apply(Algebra.Lamda.Piece.eq.Lamda.Block)

    Eq << Eq.A_def[i]

    Eq << Algebra.Cond.to.All.restrict.apply(Eq[-1], (i, 0, n - Min(u, n)))

    Eq << Algebra.All_Eq.to.All.Eq.Slice.apply(Eq[-1], slice(i, i + Min(u, n)))

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Expr.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Mul.Lamda)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul.eq.Block)

    Eq << Algebra.All_Eq.to.Eq.Lamda.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Lamda.eq.Add)

    Eq.upper_part = Eq[-1].this.find(Lamda[BlockMatrix]).apply(Algebra.Lamda.Block.eq.Block.Lamda)

    Eq << Eq.A_def[i][relu(i + 1 - l):Min(n, i + u)]

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -i)

    Eq << Eq[-1].this.find(Mul[Lamda]).apply(Algebra.Expr.eq.Lamda, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Mul.Lamda)

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.offset, -relu(i + 1 - l) + i)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Delta.eq.Block)

    Eq << Eq[-1].this.find(Mul[BlockMatrix]).apply(Algebra.Mul.eq.Block)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=1).reversed

    Eq << Eq.z_def.subs(Eq.left_upper_part.reversed, Eq.left_lower_part.reversed, Eq[-1], Eq.upper_part.reversed, Eq.lower_part)

    Eq << Keras.Eq_Block.to.Eq.Softmax.st.LogSumExp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Symbol).definition




if __name__ == '__main__':
    run()
# created on 2022-03-14
# updated on 2022-03-15


from . import tf
