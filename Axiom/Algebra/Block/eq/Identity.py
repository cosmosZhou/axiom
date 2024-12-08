from util import *


@apply
def apply(self):
    blocks = self.blocks
    for i in range(len(blocks)):
        for j in range(len(blocks[i])):
            if j == i:
                assert blocks[i][j].is_Identity or blocks[i][j].is_One
            else:
                assert blocks[i][j].is_zero
    return Equal(self, Identity(self.shape[-1]))


@prove
def prove(Eq):
    from Axiom import Algebra

    n, m = Symbol(integer=True, positive=True)
    Eq << apply(BlockMatrix([[Identity(n), ZeroMatrix(n, m)], [ZeroMatrix(m, n), Identity(m)]]))

    i = Symbol(domain=Range(n + m))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(n + m))
    Eq << Algebra.Eq.of.Eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.unnest)

    Eq << Eq[-1].this.lhs.apply(Algebra.Piece.swap, 1)

    Eq << Algebra.Cond_Piece.of.And.Imply.apply(Eq[-1])

    Eq << Algebra.Imply_Or.of.And.Imply.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Lt.Ge.to.Lt.trans), Eq[-1].this.lhs.apply(Algebra.Lt.Ge.to.Gt.trans)

    Eq << Eq[-2].this.lhs.apply(Algebra.Lt.to.Ne)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt.to.Ne)





if __name__ == '__main__':
    run()
# created on 2023-06-16
# updated on 2023-08-19
