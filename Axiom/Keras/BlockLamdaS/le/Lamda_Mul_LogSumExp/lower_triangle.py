from util import *


@apply
def apply(A, l):
    n, S[n] = A.shape
    assert A.is_real
    assert n >= 2 and l >= 2 and l <= n
    i = Symbol(integer=True)
    return BlockMatrix(
            Lamda[i:l](BlockMatrix(-oo * OneMatrix(l - i - 1), A[i, :i + 1])),
            Lamda[i:n - l](A[i + l, i + 1:i + l + 1])) <= Lamda[i:n](OneMatrix(l) * logsumexp(A[i, relu(i + 1 - l):i + 1]))


@prove
def prove(Eq):
    from Axiom import Algebra, Keras

    n = Symbol(domain=Range(2, oo))
    l = Symbol(domain=Range(2, n + 1))
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(A, l)

    Eq << Algebra.Le.of.All.Le.apply(Eq[0])

    Eq << Algebra.Le.of.Le_0.apply(Eq[-1])

    Eq << Algebra.Cond_Piece.of.Or.apply(Eq[-1])

    Eq << Eq[-1].this.find(LessEqual).apply(Algebra.Le_0.of.Le)

    Eq << Eq[-1].this.find(LessEqual[ZeroMatrix]).apply(Algebra.Le_0.of.Le)

    Eq << Eq[-1].this.find(LessEqual[BlockMatrix]).apply(Algebra.LeBlock.of.And.Le)
    Eq.ou = Eq[-1].this.find(LessEqual[Mul, logsumexp]).apply(Algebra.Le.of.All.Le)

    Eq <<= Keras.Le_LogSumExp.apply(Eq.ou.find(Sliced)), Keras.Le_LogSumExp.apply(Eq.ou.args[1].find(Sliced))

    Eq <<= Eq.ou.find(Less).this.apply(Keras.Lt.to.Eq_.Relu.Zero), Eq.ou.find(GreaterEqual).this.apply(Keras.Ge.to.Eq.Relu)

    Eq <<= Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[-2], Eq[-4]), Algebra.Cond.Imply.to.Imply.And.rhs.apply(Eq[-1], Eq[-3])

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True, index=1), Eq[-1].this.rhs.apply(Algebra.Eq.Cond.to.Cond.subs, reverse=True, index=1)

    Eq << Algebra.Imply.Imply.to.Or.apply(Eq[-2], Eq[-1])





if __name__ == '__main__':
    run()
# created on 2022-03-31
# updated on 2023-05-25
