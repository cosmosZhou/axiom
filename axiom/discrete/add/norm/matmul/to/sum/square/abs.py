from util import *


@apply
def apply(self):
    ((L, t), (S[0], k)), ((ξ, (S[k], S[t])), S[L[k:t, :k]]), S[ξ[k:t] @ ~L[k:t, :k] @ L[t, :k]] = \
    self.of(Norm[Sliced[Indexed]] ** 2 + Norm[Sliced @ Conjugate] ** 2 + 2 * Re)
    return Equal(self, Norm(BlockMatrix(ξ[k:t],1) @ ~L[k:t + 1, :k]) ** 2)

@prove
def prove(Eq):
    from axiom import discrete

    t, k = Symbol(integer=True, positive=True)
    L = Symbol(shape=(oo, oo), super_complex=True)
    ξ = Symbol(r'{\color{red} {ξ}}', complex=True, shape=(oo,))
    Eq << apply(Norm(ξ[k:t] @ ~L[k:t, :k]) ** 2 + Norm(L[t, :k]) ** 2 + 2 * Re(ξ[k:t] @ ~L[k:t, :k] @ L[t, :k]))

    Eq << Eq[0].this.rhs.apply(discrete.sum.square.abs.to.add.norm.matmul)




if __name__ == '__main__':
    run()
# created on 2023-06-24
