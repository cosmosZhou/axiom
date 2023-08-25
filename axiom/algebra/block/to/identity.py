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
    from axiom import algebra

    n, m = Symbol(integer=True, positive=True)
    Eq << apply(BlockMatrix([[Identity(n), ZeroMatrix(n, m)], [ZeroMatrix(m, n), Identity(m)]]))

    i = Symbol(domain=Range(n + m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[0], i)

    j = Symbol(domain=Range(n + m))
    Eq << algebra.eq.given.eq.getitem.apply(Eq[-1], j)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.unnest)

    Eq << Eq[-1].this.lhs.apply(algebra.piece.swap, 1)

    Eq << algebra.cond_piece.given.et.infer.apply(Eq[-1])

    Eq << algebra.infer_ou.given.et.infer.apply(Eq[-1])

    Eq <<= Eq[-2].this.lhs.apply(algebra.lt.ge.imply.lt.transit), Eq[-1].this.lhs.apply(algebra.lt.ge.imply.gt.transit)

    Eq << Eq[-2].this.lhs.apply(algebra.lt.imply.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.gt.imply.ne)

    
    


if __name__ == '__main__':
    run()
# created on 2023-06-16
# updated on 2023-08-19
