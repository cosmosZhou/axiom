from util import *


@apply
def apply(infer, j=None):
    x, (S[~x], A, S[x]) = infer.of(Infer[Unequal[0], MatMul > 0])
    if j is None:
        j = infer.generate_var(integer=True)
    return A[j, j] > 0

@prove
def prove(Eq):
    from axiom import algebra, discrete

    n = Symbol(integer=True, positive=True)
    A = Symbol(shape=(n, n), complex=True)
    x = Symbol(shape=(n,), complex=True)
    i = Symbol(integer=True)
    Eq << apply(Infer(Unequal(x, ZeroMatrix(n)), (~x) @ A @ x > 0), i)

    j = Symbol(domain=Range(n))
    Eq << Eq[0].subs(x, Lamda[i:n](KroneckerDelta(i, j)))

    Eq << Eq[-1].this.lhs.apply(algebra.ne.given.any.ne)

    Eq << Eq[-1].this.lhs.apply(algebra.any.given.cond.subs, i, j)

    Eq << Eq[-1].this.lhs.args[:2].apply(discrete.matmul.to.lamda)

    Eq << Eq[-1].this.lhs.apply(discrete.matmul.to.sum)

    Eq << algebra.cond.imply.all.apply(Eq[-1], j)

    j = Eq[-1].lhs.index
    Eq << Eq[-1].subs(j, i)

    


if __name__ == '__main__':
    run()
# created on 2023-05-01
