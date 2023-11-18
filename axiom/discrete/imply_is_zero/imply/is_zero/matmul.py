from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Infer[Greater, Equal[Indexed, 0]])
    return Equal(L[i, Min(i, j) + 1:] @ ~L[j, Min(i, j) + 1:], 0)

@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Infer(j > i, Equal(L[i, j], 0)))

    Eq << algebra.cond.given.et.infer.split.apply(Eq[-1], cond=j > i)

    Eq <<= Eq[-2].this.lhs.apply(algebra.gt.imply.eq.min, ret=0), Eq[-1].this.lhs.apply(algebra.le.imply.eq.min, ret=0)

    Eq <<= algebra.infer_et.given.infer.et.subs.apply(Eq[-2]), algebra.infer_et.given.infer.et.subs.apply(Eq[-1])

    Eq <<= algebra.infer_et.given.infer.delete.apply(Eq[-2], 0), algebra.infer_et.given.infer.delete.apply(Eq[-1], 0)

    Eq <<= algebra.infer.given.all.apply(Eq[-2], i), algebra.infer.given.all.apply(Eq[-1], j)

    Eq << algebra.infer_is_zero.imply.is_zero.slice.apply(Eq[0])

    Eq << Eq[-1].subs(i, j)

    Eq <<= Eq[-4].subs(Eq[-2]), Eq[-3].subs(Eq[-1])

    
    


if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
