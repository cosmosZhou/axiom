from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Imply[Greater, Equal[Indexed, 0]])
    return Equal(L[i, Min(i, j) + 1:] @ ~L[j, Min(i, j) + 1:], 0)

@prove
def prove(Eq):
    from Axiom import Algebra

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Imply(j > i, Equal(L[i, j], 0)))

    Eq << Algebra.Cond.of.And.Imply.split.apply(Eq[-1], cond=j > i)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Gt.to.Eq.Min, ret=0), Eq[-1].this.lhs.apply(Algebra.Le.to.Eq.Min, ret=0)

    Eq <<= Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-2]), Algebra.Imply_And.of.Imply.And.subs.apply(Eq[-1])

    Eq <<= Algebra.Imply_And.of.Imply.delete.apply(Eq[-2], 0), Algebra.Imply_And.of.Imply.delete.apply(Eq[-1], 0)

    Eq <<= Algebra.Imply.of.All.apply(Eq[-2], i), Algebra.Imply.of.All.apply(Eq[-1], j)

    Eq << Algebra.Imply_Eq_0.to.Eq_0.Slice.apply(Eq[0])

    Eq << Eq[-1].subs(i, j)

    Eq <<= Eq[-4].subs(Eq[-2]), Eq[-3].subs(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
