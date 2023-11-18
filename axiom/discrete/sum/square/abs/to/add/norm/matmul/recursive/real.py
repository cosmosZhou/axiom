from util import *


@apply
def apply(self):
    (ξ, (k, t)), (L, (S[k], S[t + 1]), (S[0], S[k])) = self.of(Norm[BlockMatrix[Sliced, One] @ Sliced] ** 2)

    return Equal(self, abs(ξ[k]) ** 2 * Norm(L[k, :k]) ** 2 + Norm(BlockMatrix(ξ[k + 1:t],1) @ L[k + 1:t + 1, :k]) ** 2 + 2 * (BlockMatrix(ξ[k + 1:t],1) @ ~L[k + 1:t + 1, :k] @ L[k, :k]) * ξ[k])

@prove
def prove(Eq):
    from axiom import algebra, discrete

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_real=True)
    ξ = Symbol(r'{\color{red} {ξ}}', real=True, shape=(oo,))
    Eq << apply(Norm(BlockMatrix(ξ[k:t],1) @ L[k:t + 1, :k]) ** 2)

    Eq << Eq[0].lhs.this.find(Sliced).apply(algebra.expr.to.block, t - k)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq.next = Eq[-1].subs(k, k + 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.add.shift)

    Eq << Eq[-1].this.rhs.apply(discrete.square.norm.to.add.matmul)

    Eq << Eq[-1].this.rhs.find(Norm[Indexed * Sliced]).apply(algebra.norm.to.mul.norm)

    Eq << Eq[-1].this.rhs.args[-2:].apply(discrete.add.square.to.sub.matmul)

    Eq << Eq[-1].this.rhs.find(Mul[~MatMul[Transpose]]).T

    Eq << Eq[-1].this.rhs.args[1:3].apply(algebra.add.to.mul)

    Eq << Eq[-1].this.find(Mul[~Add]).apply(discrete.add.to.matmul)

    Eq << Eq[-1].rhs.find(Add[MatMul]).this.apply(discrete.add.to.matmul.block)

    Eq << Eq[-2].subs(Eq[-1])






if __name__ == '__main__':
    run()
# created on 2023-06-30
