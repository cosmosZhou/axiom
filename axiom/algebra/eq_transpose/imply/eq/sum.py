from util import *


@apply
def apply(eq, i, j):
    A, S[A.T] = eq.of(Equal)
    n = A.shape[-1]
    return Equal(ReducedSum(ReducedSum(A)), Sum[i:n](A[i, i]) + 2 * Sum[j:i, i:n](A[i, j]))

@prove
def prove(Eq):
    from axiom import algebra

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    i, j = Symbol(integer=True)
    Eq << apply(Equal(A, A.T), i, j)

    Eq << Eq[1].lhs.this.apply(algebra.reducedSum.to.sum, i)

    Eq << Eq[-1].this.rhs.find(ReducedSum).apply(algebra.reducedSum.to.sum, j)

    Eq << Eq[-1].this.rhs.apply(algebra.sum.to.add.split.limits)

    Eq << Eq[0][j, i]

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Sum[2]).apply(algebra.sum.to.mul)

    


if __name__ == '__main__':
    run()
# created on 2023-05-25
