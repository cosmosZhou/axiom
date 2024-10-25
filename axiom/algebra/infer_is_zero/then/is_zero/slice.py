from util import *


@apply
def apply(self):
    (j, i), (L, S[i], S[j]) = self.of(Infer[Greater, Equal[Indexed, 0]])
    n = L.shape[1]
    return Equal(L[i, i + 1:], ZeroMatrix(n - i - 1))

@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    L = Symbol(shape=(n, n), super_complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Infer(j > i, Equal(L[i, j], 0)))

    Eq << algebra.infer.then.all.apply(Eq[0], j)

    Eq << algebra.all.then.all.limits.domain_defined.apply(Eq[-1], j)

    Eq << Eq[-1].this(i).find(Max).simplify()

    Eq << algebra.all_eq.then.eq.lamda.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-06-23
# updated on 2023-06-27
