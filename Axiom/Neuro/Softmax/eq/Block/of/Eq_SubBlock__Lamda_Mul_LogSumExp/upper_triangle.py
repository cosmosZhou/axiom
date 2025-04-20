from util import *


@apply
def apply(eq):
    (((((A, i), (S[i], (S[i], u))), (S[i], S[0], (n,  S[u]))), (A[i + n - u, i + n - u:], (S[i], S[0], S[u]))), (A[i, i:Min(n, i + u)], (S[i], S[0], S[n]))), z = \
    eq.of(Equal[
        BlockMatrix[
            Lamda[
                Sliced[Indexed, Tuple[Add]],
                Tuple[Expr - Expr]
            ],
            Lamda[
                BlockMatrix[NegativeInfinity * OneMatrix]
            ]
        ] - Lamda[OneMatrix * logsumexp]])

    assert n >= 2 and u >= 2 and u <= n

    return Equal(softmax(A + (BandPart[0, u - 1](OneMatrix(n, n)) - 1) * oo), BlockMatrix(
        Lamda[i:n - u](BlockMatrix(ZeroMatrix(i), Exp(z[i]), ZeroMatrix(n - i - u))),
        Lamda[i:u](BlockMatrix(ZeroMatrix(n - u + i), Exp(z[i + n - u, :u - i])))))


@prove
def prove(Eq):
    from Axiom import Algebra, Neuro

    n = Symbol(domain=Range(2, oo))
    u = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    z = Symbol(shape=(n, u), extended_real=True)
    i = Symbol(integer=True)
    Eq << apply(Equal(z, BlockMatrix(
        Lamda[i:n - u](A[i, i:i + u]),
        Lamda[i:u](BlockMatrix(A[i + n - u, n - u + i:], -oo * OneMatrix(i)))) - Lamda[i:n](OneMatrix(u) * logsumexp(A[i, i:Min(n, i + u)]))))

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

    Eq << Neuro.Softmax.eq.Block.of.Eq_Div_Lamda_Mul_ReducedSumExp.upper_triangle.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-01-03
# updated on 2023-05-20
