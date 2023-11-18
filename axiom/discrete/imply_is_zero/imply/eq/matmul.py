from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Infer[Greater, Equal[Indexed, 0]])
    return Equal(L[i] @ ~L[j],  L[i, :Min(i, j) + 1] @ ~L[j, :Min(i, j) + 1])

@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Infer(j > i, Equal(L[i, j], 0)))

    Eq << Eq[-1].this.lhs.args[0].apply(algebra.expr.to.block, Min(i, j) + 1)

    Eq << Eq[-1].this.lhs.args[1].apply(algebra.expr.to.block, Min(i, j) + 1)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.block)

    Eq << discrete.imply_is_zero.imply.is_zero.matmul.apply(Eq[0])

    
    


if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
