from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], (n, u)))), (S[i], S[0], (S[1], S[n],  S[-Min(n, u)]))), (S[A[i + n - Min(n, u) + 1][i + n - Min(n, u) + 1:n]], (S[i], S[0], S[Min(n, u) - 1]))), (S[A[i][i:Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[
                Sliced[Indexed, Tuple[Add[Min]]],
                Tuple[Add]
            ],
            Lamda[
                BlockMatrix[NegativeInfinity * OneMatrix]
            ]
        ] - Lamda[OneMatrix * logsumexp]
    ])

    assert n >= 2 and u >= 2
    breadth = Min(u, n) - 1
    return Equal(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:n - breadth](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - 1 - i - breadth))),
        Lamda[i:breadth](BlockMatrix(ZeroMatrix(n - breadth + i), Exp(z[i + n - breadth, :breadth - i])))))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro

    n, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, Min(u, n)), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
        Lamda[i:n - Min(u, n) + 1](A[i, i:i + Min(u, n)]),
        Lamda[i:Min(u, n) - 1](BlockMatrix(A[i + n - Min(u, n) + 1, n - Min(u, n) + i + 1:], -oo * OneMatrix(i + 1)))) - Lamda[i:n](OneMatrix(Min(u, n)) * logsumexp(A[i, i:Min(n, i + u)]))))

    Eq << Algebra.EqExp.of.Eq.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Lamda[BlockMatrix]]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Lamda]]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.OneMatrix)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(Algebra.Lamda.eq.Pow)

    Eq << Neuro.Softmax.eq.Block.of.Eq_Div_Lamda_ReducedSumExp.upper_triangle.tf.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-12
