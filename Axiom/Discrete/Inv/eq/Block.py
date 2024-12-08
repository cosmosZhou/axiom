from util import *


@apply
def apply(self):
    blocks = self.of(MatPow[Expr, -1]).blocks
    index = -1
    is_lower = None
    for i in range(len(blocks)):
        blocks[i] = [*blocks[i]]
        for j in range(len(blocks[i])):
            if j == i:
                assert blocks[i][j].is_Identity or blocks[i][j].is_One
            elif blocks[i][j].is_zero:
                ...
            elif index >= 0:
                assert j == index
            else:
                index = j
                blocks[i][j] = -blocks[i][j]
                if is_lower is None:
                    is_lower = i < j
                else:
                    assert is_lower == i < j

    return Equal(self, BlockMatrix(blocks))

@prove
def prove(Eq):
    from Axiom import Discrete, Algebra

    n, k, l = Symbol(integer=True, positive=True)
    # X = Symbol(real=True, shape=(n - k - l, l))
    X = Symbol(real=True, shape=(k, l))
    Eq << apply(
        BlockMatrix([
            [Identity(k), X, ZeroMatrix(k, n - k - l)],
            [ZeroMatrix(l, k), Identity(l), ZeroMatrix(l, n - k - l)],
            [ZeroMatrix(n - k - l, k), ZeroMatrix(n - k - l, l), Identity(n - k - l)]
        ]) ^ -1)

    Eq << (Eq[0].lhs.find(BlockMatrix) @ Eq[0].rhs).this.apply(Discrete.Dot.eq.Block, True)

    Eq << Eq[-1].this.rhs.apply(Algebra.Block.eq.Identity)

    Eq << Discrete.Eq_Dot.to.Eq.Inv.apply(Eq[-1], left=True)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2023-07-11
# updated on 2023-08-19
