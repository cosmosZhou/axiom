from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Imply[Greater, Equal[Indexed, 0]])
    return Equal(L[i] @ ~L[j],  L[i, :Min(i, j) + 1] @ ~L[j, :Min(i, j) + 1])

@prove
def prove(Eq):
    from Axiom import Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Imply(j > i, Equal(L[i, j], 0)))

    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Expr.eq.Block, Min(i, j) + 1)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Expr.eq.Block, Min(i, j) + 1)

    Eq << Eq[-1].this.lhs.apply(Discrete.Dot.eq.Block)

    Eq << Discrete.Imply_Eq_0.to.Eq_0.Dot.apply(Eq[0])





if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
