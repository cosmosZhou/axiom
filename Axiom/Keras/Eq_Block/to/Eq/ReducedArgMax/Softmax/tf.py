from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n) - 1, i:i + Min(l, n) - 1]], (S[i], S[0], S[n - Min(l, n) + 1]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[1], S[n], S[-Min(n, u)]))), (((S[A], S[i + n - Min(n, u) + 1]), (S[i + n - Min(n, u) + 1], S[n])), (S[i], S[0], (S[n], S[u]))))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
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
            Lamda[Sliced[Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    Sliced[Indexed],
                    NegativeInfinity * OneMatrix
                    ],
                Tuple[Min - 1]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and l >= 2 and u >= 2
    return Equal(ReducedArgMax(softmax(A + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo)) - Lamda[i:n](i), ReducedArgMax(z) - Min(l, n) + 1)


@prove
def prove(Eq):
    from Axiom import Keras, Algebra, Sets

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n) - 1](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i, :i])),
            Lamda[i:n - Min(l, n) + 1](A[i + Min(l, n) - 1, i:i + Min(l, n) - 1])),
        BlockMatrix(
            Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1))))) - Lamda[i:n](OneMatrix(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))))

    Eq << Keras.Eq_Block.to.Eq.Softmax.st.LogSumExp.tf.apply(Eq[0])

    z_quote = Symbol(Eq[-1].lhs)
    Eq.z_quote_def = z_quote.this.definition

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.z_quote_def, Eq[-1])

    Eq << Eq[-1][i]

    Eq.four_blocks = Eq[-1].this.rhs.apply(Algebra.Add.Piece.eq.Piece)

    j = Symbol(integer=True)
    Eq << Eq.four_blocks.find(Add[BlockMatrix]).this.apply(Algebra.Expr.eq.Lamda, j)

    Eq << Eq[-1].this.find(Piecewise[2]).apply(Algebra.Piece.swap, 0)

    Eq.block0 = Eq[-1].this.rhs.apply(Algebra.Lamda.Piece.eq.Block)

    Eq << Eq.four_blocks.find(ExprCondPair[2]).find(BlockMatrix).this.apply(Algebra.Expr.eq.Lamda, j)

    Eq.block1 = Eq[-1].this.rhs.apply(Algebra.Lamda.eq.Exp)

    Eq << Eq.four_blocks.find(ExprCondPair[3]).find(Add[BlockMatrix]).this.apply(Algebra.Expr.eq.Lamda, j)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap, 0)

    Eq << Eq[-1].this.find(Piecewise).apply(Algebra.Piece.swap, 0)

    Eq << Eq[-1].this.find(And).apply(Algebra.And.equ.Or)

    Eq.block2 = Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Piece.eq.Block)

    Eq << Eq.four_blocks.find(ExprCondPair[4]).find(Add[BlockMatrix]).this.apply(Algebra.Expr.eq.Lamda, j)

    Eq << Eq[-1].this.find(Piecewise[ExprCondPair[3]]).apply(Algebra.Piece.swap, 1)

    Eq << Eq[-1].this.find(Add[Piecewise]).apply(Algebra.Add.Piece.eq.Piece)

    Eq.block3 = Eq[-1].this.find(Lamda).apply(Algebra.Lamda.Piece.eq.Block)

    Eq << Eq.four_blocks.subs(Eq.block0, Eq.block1, Eq.block2, Eq.block3)

    Eq << Algebra.Eq.to.Eq.ReducedArgMax.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.ReducedArgMax.eq.Piece.ReducedArgMax)

    Eq << Eq[-1].this.rhs.find(ReducedArgMax).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(ReducedArgMax[Exp]).apply(Algebra.ReducedArgMax.Exp.eq.ReducedArgMax)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.swap, -2)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.And.invert, 1)

    Eq << Eq[-1].this.rhs.apply(Algebra.Piece.And.invert)

    Eq << Eq[-1].this.find(And).apply(Algebra.Lt.Lt.equ.Lt.Min)

    Eq << Eq[-1].this.find(And).apply(Sets.Cond.Cond.equ.In.Range)

    Eq.four_blocks = Eq[-1].this.find(And).apply(Algebra.Ge.Ge.equ.Ge.Max)

    Eq << Keras.Eq_Block.to.And.Imply.Block.tf.apply(Eq[0])

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Eq.to.Eq.ReducedArgMax), Eq[-2].this.rhs.apply(Algebra.Eq.to.Eq.ReducedArgMax), Eq[-1].this.rhs.apply(Algebra.Eq.to.Eq.ReducedArgMax)

    Eq <<= Eq[-3].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add), \
        Eq[-2].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.Add)

    Eq.block3 = Eq[-3].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq.block0 = Eq[-2].this.rhs.apply(Algebra.Eq.transport, rhs=slice(0, 3))

    Eq << Eq[-1].this.rhs.find(ReducedArgMax[BlockMatrix]).apply(Algebra.ReducedArgMax.Block.eq.ReducedArgMax)

    Eq.block1 = Eq[-1].this.rhs.apply(Algebra.Eq.transport, rhs=slice(0, 3))

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq.block0, Eq.four_blocks.rhs, index=0, reverse=True)

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq.block1, Eq[-1].rhs, index=1, reverse=True)

    Eq << Algebra.Imply.to.Eq.Piece.apply(Eq.block3, Eq[-1].rhs, index=1, reverse=True)

    Eq << Algebra.And.to.Eq.trans.apply(Eq.four_blocks & Eq[-1] & Eq[-2] & Eq[-3]).reversed

    Eq << Algebra.Eq.to.Eq.Lamda.apply(Eq[-1], (i, 0, n))

    Eq << Eq[-1].this.lhs.apply(Algebra.Lamda.eq.ReducedArgMax)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Add)

    Eq << Eq[-1].this.find(Lamda[ReducedArgMax]).apply(Algebra.Lamda.eq.ReducedArgMax)

    Eq << Eq[-1].subs(Eq.z_quote_def)

    Eq << Eq[-1].this.apply(Algebra.Eq.transport, rhs=3)





if __name__ == '__main__':
    run()
# created on 2022-01-04
# updated on 2023-05-20