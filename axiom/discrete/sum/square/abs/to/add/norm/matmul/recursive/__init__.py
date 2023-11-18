from util import *


@apply
def apply(self):
    (ξ, (k, t)), (L, (S[k], S[t + 1]), (S[0], S[k])) = self.of(Norm[BlockMatrix[Sliced, One] @ Conjugate[Sliced]] ** 2)

    return Equal(self, abs(ξ[k]) ** 2 * Norm(L[k, :k]) ** 2 + Norm(BlockMatrix(ξ[k + 1:t],1) @ ~L[k + 1:t + 1, :k]) ** 2 + 2 * Re((BlockMatrix(ξ[k + 1:t],1) @ ~L[k + 1:t + 1, :k] @ L[k, :k]) * ~ξ[k]))

@prove
def prove(Eq):
    from axiom import algebra, discrete

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_complex=True)
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << apply(Norm(BlockMatrix(ξ[k:t],1) @ ~L[k:t + 1, :k]) ** 2)

    Eq << Eq[0].lhs.this.find(Conjugate[~Sliced]).apply(algebra.expr.to.block, t - k)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.block)

    Eq.next = Eq[-1].subs(k, k + 1)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(discrete.matmul.to.add.shift)

    Eq << Eq[-1].this.rhs.apply(discrete.square.norm.to.add.matmul)

    Eq << Eq[-1].this.rhs.find(Norm[Indexed * Conjugate]).apply(algebra.norm.to.mul.norm)

    Eq << Eq[-1].this.rhs.args[1:3].apply(discrete.add.square.to.sub.matmul)

    Eq << Eq[-1].this.rhs.find(Re[Mul[~MatMul[Adjoint]]]).T

    Eq << Eq[-1].this.rhs.find(Re[MatMul * Conjugate]).apply(algebra.re.conj)

    Eq << Eq[-1].this.rhs.args[-2:].apply(algebra.add.to.re)

    Eq << Eq[-1].this.rhs.args[-1].apply(algebra.re.to.mul)

    Eq << Eq[-1].this.rhs.args[-1].find(Add).apply(discrete.add.to.matmul)

    Eq << Eq[-1].this.find(Re).apply(algebra.re.conj)

    Eq << Eq[-1].rhs.find(Add[MatMul]).this.apply(discrete.add.to.matmul.block)

    Eq << Eq[-1].this.rhs.find(BlockMatrix[Conjugate]).apply(algebra.block.to.conj)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.find(Norm[Conjugate]).apply(algebra.norm.conj)

    
    


if __name__ == '__main__':
    run()
# created on 2023-06-24
# updated on 2023-09-19
from . import real
