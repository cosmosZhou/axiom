from util import *


@apply
def apply(eq):
    ((Λ_x, Λ_xy), (S[Λ_xy.T], Λ_y)), ((Σ_x, Σ_xy), (S[Σ_xy.T], Σ_y)) = eq.of(Equal[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], MatPow[BlockMatrix[BlockMatrix[1], BlockMatrix[1]], -1]])
    assert Σ_x.is_invertible and Σ_y.is_invertible
    return Equal(Λ_x, (Σ_x - Σ_xy @ (Σ_y ^ -1) @ Σ_xy.T) ^ -1), \
        Equal(Λ_y, (Σ_y - Σ_xy.T @ (Σ_x ^ -1) @ Σ_xy) ^ -1), \
        Equal(Λ_xy, -Λ_x @ Σ_xy @ (Σ_y ^ -1)), \
        Equal(Λ_xy.T, -Λ_y @ Σ_xy.T @ (Σ_x ^ -1))

@prove
def prove(Eq):
    from axiom import discrete, algebra

    m, n = Symbol(integer=True, positive=True)
    Σ_x = Symbol(shape=(n, n), real=True, singular=False)
    Λ_x = Symbol(shape=(n, n), real=True)
    Σ_y = Symbol(shape=(m, m), real=True, singular=False)
    Λ_y = Symbol(shape=(m, m), real=True)
    Σ_xy, Λ_xy = Symbol(shape=(n, m), real=True)
    Eq << apply(Equal(BlockMatrix([[Λ_x, Λ_xy], [Λ_xy.T, Λ_y]]), Inverse(BlockMatrix([[Σ_x, Σ_xy], [Σ_xy.T, Σ_y]]))))

    Eq << Eq[0].reversed

    Eq << discrete.eq.then.eq.matmul.apply(Eq[-1], Eq[-1].lhs.find(BlockMatrix)).reversed

    Eq << Eq[-1].this.rhs.apply(algebra.expr.to.block, n, n)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.block, deep=True)

    Eq << algebra.eq.then.et.eq.split.apply(Eq[-1], n)

    Eq <<= algebra.eq.then.eq.transpose.apply(Eq[-2]), algebra.eq.then.eq.transpose.apply(Eq[-1])

    Eq <<= algebra.eq.then.et.eq.split.apply(Eq[-2], n), algebra.eq.then.et.eq.split.apply(Eq[-1], n)

    Eq.eq_identity_x = Eq[-4].T

    Eq.is_zero_xy = Eq[-3].T

    Eq.is_zero_yx = Eq[-2].T

    Eq.eq_identity_y = Eq[-1].T

    Eq <<= algebra.eq.then.eq.transport.apply(Eq.is_zero_xy, 0), algebra.eq.then.eq.transport.apply(Eq.is_zero_yx, 0)

    Eq << Eq[-2] @ (Σ_y ^ -1)

    Eq << Eq[-1] @ (Σ_x ^ -1)

    Eq <<= Eq.eq_identity_x.subs(Eq[3]), Eq.eq_identity_y.subs(Eq[4])

    Eq <<= Eq[-2].this.lhs.apply(discrete.add.to.matmul), Eq[-1].this.lhs.apply(discrete.add.to.matmul)

    Eq <<= discrete.eq_matmul.then.eq.inverse.apply(Eq[-2]), discrete.eq_matmul.then.eq.inverse.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-04-28
# updated on 2023-04-30
from . import transpose
