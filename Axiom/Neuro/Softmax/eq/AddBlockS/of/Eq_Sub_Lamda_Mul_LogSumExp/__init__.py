from util import *


@apply
def apply(eq):
    ((((((A, i), (S[0], S[i])), (S[i], S[0], (l, n))), (S[A[i + Min(l, n), i + 1:i + Min(l, n)]], (S[i], S[0], S[n - Min(l, n)]))), (((S[A[i]], (S[i], (S[i], (S[n], u)))), (S[i], S[0], (S[n], S[-Min(n, u)]))), (S[A[i + n - Min(n, u), i + n - Min(n, u):n]], (S[i], S[0], S[Min(n, u)])))), (S[A[i][relu(i - l + 1):Min(n, i + u)]], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[BlockMatrix[1][
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
            Lamda[Sliced[Tuple[Add[Min]]], Tuple[Add]],
            Lamda[
                BlockMatrix[
                    NegativeInfinity * OneMatrix
                    ]
                ]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2 and l >= 2
    breadth = Add(Min(l, n), Min(u, n), -1)
    return Equal(softmax(A + (BandPart[l - 1, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:Min(l, n)](BlockMatrix(Exp(z[i, Min(l, n) - i - 1:Min(l, n) - 1]), ZeroMatrix(n - i))),
        Lamda[i:n - Min(l, n)](BlockMatrix(ZeroMatrix(i + 1), Exp(z[i + Min(l, n), :Min(l, n) - 1]), ZeroMatrix(n - i - Min(l, n))))) + BlockMatrix(
        Lamda[i:n - Min(u, n)](BlockMatrix(ZeroMatrix(i), Exp(z[i, Min(l, n) - 1:]), ZeroMatrix(n - i - Min(u, n)))),
        Lamda[i:Min(u, n)](BlockMatrix(ZeroMatrix(n - Min(u, n) + i), Exp(z[i + n - Min(u, n), Min(l, n) - 1:breadth - i])))))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro

    n, l, u = Symbol(domain=Range(2, oo))
    A = Symbol(shape=(n, n), real=True)
    i = Symbol(integer=True)
    breadth = Add(Min(l, n), Min(u, n), -1)
    z = Symbol(shape=(n, breadth), extended_real=True)
    Eq << apply(Equal(z, BlockMatrix[1](
        BlockMatrix(
            Lamda[i:Min(l, n)](BlockMatrix(-oo * OneMatrix(Min(l, n) - i - 1), A[i, :i])),
            Lamda[i:n - Min(l, n)](A[i + Min(l, n), i + 1:i + Min(l, n)])),
        BlockMatrix(
            Lamda[i:n - Min(u, n)](A[i, i:i + Min(u, n)]),
            Lamda[i:Min(u, n)](BlockMatrix(A[i + n - Min(u, n), n - Min(u, n) + i:], -oo * OneMatrix(i))))) - Lamda[i:n](OneMatrix(breadth) * logsumexp(A[i, relu(i + 1 - l):Min(n, i + u)]))))

    Eq << Algebra.EqExp.of.Eq.apply(Eq[0])

    Eq << Eq[-1].this.rhs.apply(Algebra.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Lamda[BlockMatrix]]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.find(Exp[Lamda]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.find(Exp[BlockMatrix]).apply(Algebra.Exp.eq.Block)

    Eq << Eq[-1].this.find(logsumexp).defun()

    Eq << Eq[-1].this.rhs.find(Exp[Mul[Lamda]]).apply(Algebra.Exp.eq.Lamda)

    Eq << Eq[-1].this.rhs.find(Pow[ReducedSum]).apply(Algebra.Pow.eq.Mul.OneMatrix)

    Eq << Eq[-1].this.rhs.find(Lamda).apply(Algebra.Lamda.eq.Pow)

    Eq << Neuro.Softmax.eq.AddBlockS.of.Eq_DivBlock__Lamda_Mul_ReducedSumExpIndexed_SlicedRelu.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-06-08



from . import tf
