from util import *


@apply
def apply(self):
    A, B = self.of(Determinant[Expr @ Expr])

    return Equal(self, Det(A) * Det(B))


@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n = Symbol(integer=True, positive=True)
    A, B = Symbol(shape=(n, n), complex=True)
    Eq << apply(Determinant(A @ B))

    Eq << (BlockMatrix([[A, ZeroMatrix(n, n)], [Identity(n), B]]) @ BlockMatrix([[Identity(n), -B], [ZeroMatrix(n, n), Identity(n)]])).this.apply(Discrete.Dot.eq.Block, deep=True)

    Eq << Discrete.Eq.to.Eq.Det.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.Dot.simp.col_transformation)

    Eq << Eq[-1].this.lhs.apply(Discrete.Det.Block.eq.Mul.deux)

    Eq << Eq[-1].this.rhs.apply(Discrete.Det.Block.eq.Mul.deux)

    Eq << Eq[-1].this.rhs.find(Det).apply(Discrete.Det.Mul.eq.Mul)

    Eq << Eq[-1].this.find(Pow).apply(Algebra.Pow.eq.One)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2020-08-20
# updated on 2021-12-13