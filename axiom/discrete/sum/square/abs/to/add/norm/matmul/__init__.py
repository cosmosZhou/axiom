from util import *


@apply
def apply(self):
    (ξ, (k, t)), (L, (S[k], S[t + 1]), (S[0], S[k])) = \
    self.of(Norm[BlockMatrix[Sliced, One] @ Conjugate[Sliced]] ** 2)
    return Equal(self, Norm(ξ[k:t] @ ~L[k:t, :k]) ** 2 + Norm(L[t, :k]) ** 2 + 2 * Re(ξ[k:t] @ ~L[k:t, :k] @ L[t, :k]))

@prove
def prove(Eq):
    from axiom import algebra, discrete

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_complex=True)
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << apply(Norm(BlockMatrix(ξ[k:t],1) @ ~L[k:t + 1, :k]) ** 2)

    Eq << Eq[0].lhs.this.find(Conjugate[~Sliced]).apply(algebra.expr.to.block, t - k)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq << Eq[-1].this.rhs.apply(discrete.square.norm.to.add.matmul)

    Eq << Eq[-1].this.find(Re[~MatMul]).T

    Eq << Eq[-1].this.find(Norm[Conjugate]).apply(algebra.norm.conj)




if __name__ == '__main__':
    run()
# created on 2023-06-24
from . import recursive
