from util import *


@apply
def apply(self):
    (Q, one), W, (KT, S[one]) = self.of(BlockMatrix[1] @ Expr @ BlockMatrix)
    K = KT.T
    n, d_z = Q.shape

    return Equal(self, Q @ W[:d_z,:d_z] @ K.T + (OneMatrix(n, d_z) * W[d_z][:d_z]) @ K.T + ((W[:d_z, d_z] @ Q.T) * OneMatrix(n, n)).T + W[d_z, d_z])


@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    n, d_z = Symbol(integer=True, positive=True)
    Q = Symbol(shape=(n, d_z), real=True)
    K = Symbol(shape=(n, d_z), real=True)
    W = Symbol(shape=(d_z + 1, d_z + 1), real=True)
    A = Symbol(shape=(n, n), real=True)
    Eq << apply(BlockMatrix[1](Q, OneMatrix(n)) @ W @ BlockMatrix[1](K, OneMatrix(n)).T)

    i, j = Symbol(integer=True)
    A = Symbol(Eq[0].lhs)
    Eq << A.this.definition

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.Expr.eq.Lamda, i, j)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Block.split, d_z, simplify=None)

    Eq << Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Block.split, d_z, axis=1)

    Eq.A_def_expand = Eq[-1].this.find(Lamda).apply(Algebra.Lamda.eq.Block.split, d_z)

    Eq << MatMul(*Eq.A_def_expand.find(MatMul).args[:2]).this.apply(Discrete.Dot.eq.Block, deep=True)

    Eq << Eq[-1] @ Eq[-2].find(MatMul).args[2]

    Eq << Eq[-1].this.rhs.apply(Discrete.Dot.eq.Block, deep=True)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq.A_def_expand, Eq[-1])

    Eq << Eq[-1].this.find(MatMul[Add]).apply(Discrete.Dot.eq.Add)

    Eq << Eq[-1].this.find(Transpose[~Mul]).apply(Algebra.Mul.eq.Add)

    Eq << Algebra.Eq.Eq.to.Eq.trans.apply(Eq[1], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-12-16
# updated on 2021-12-22
